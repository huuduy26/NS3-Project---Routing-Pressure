// scratch/noc-topology.cc
//
// 2D mesh NoC-like topology on ns-3 point-to-point links.
// Node IDs: ID = y * width + x, origin at top-left, X east, Y south.
//
// Mapping ns-3 to Tang et al. (2015):
//  - 1 "cycle" = 1 ns (g_cycleTime).
//  - Each NoC packet has len = 8 flits.
//  - Channel flit rate frate = 0.5 flits/cycle => 2 cycles per flit.
//  - So each packet takes len / frate = 16 cycles per channel.
//  - We use packetSize = 32 bytes (256 bits) and DataRate = 16Gbps,
//    so one packet serialization time is 16 ns = 16 cycles.
//
//  PIR (packet injection rate) is in packets / (node * cycle), same
//  meaning as the paper. The negative exponential inter-arrival
//  process (Poisson traffic) is used.
//
//  Simulation: each node runs a NoC router app that
//    - injects packets as a Poisson process,
//    - forwards hop-by-hop using XY / YX / OE / NF logic.
//
//  Metrics: we compute
//    - average packet latency in cycles,
//    - throughput in flits / (node * cycle),
//    - routing pressure φ by enumerating *all minimal paths*
//      allowed by the selected routing algorithm for the traffic,
//      then PIR_max = (frate / len) / φ.

#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/point-to-point-module.h"
#include "ns3/mobility-module.h"
#include "ns3/netanim-module.h"

#include <vector>
#include <map>
#include <limits>
#include <cctype>
#include <cmath>
#include <utility>
#include <sstream>

using namespace ns3;

NS_LOG_COMPONENT_DEFINE ("NoCTopology");

// ---------------------------------------------------------------------
// Coordinate helpers: ID = y * width + x  (origin at top-left)
// ---------------------------------------------------------------------

struct Coord
{
  uint32_t x;
  uint32_t y;
};

static inline Coord
IdxToCoord (uint32_t idx, uint32_t width)
{
  Coord c;
  c.x = idx % width;     // column (X)
  c.y = idx / width;     // row    (Y)
  return c;
}

static inline uint32_t
CoordToIdx (uint32_t x, uint32_t y, uint32_t width)
{
  return y * width + x;
}

static inline Coord
MoveOneStep (Coord c, int dir) // 1=E,2=W,3=N,4=S  (see enum below)
{
  switch (dir)
    {
    case 1: c.x += 1; break; // E
    case 2: c.x -= 1; break; // W
    case 3: c.y -= 1; break; // N
    case 4: c.y += 1; break; // S
    default: break;
    }
  return c;
}

static inline bool
InBounds (Coord c, uint32_t width, uint32_t height)
{
  return (c.x < width && c.y < height);
}

// ---------------------------------------------------------------------
// Tag to carry send time with each packet (for latency measurement)
// ---------------------------------------------------------------------

class SendTimeTag : public Tag
{
public:
  static TypeId GetTypeId (void)
  {
    static TypeId tid = TypeId ("ns3::SendTimeTag")
      .SetParent<Tag> ()
      .SetGroupName ("NoC")
      .AddConstructor<SendTimeTag> ();
    return tid;
  }

  virtual TypeId GetInstanceTypeId (void) const override
  {
    return GetTypeId ();
  }

  virtual uint32_t GetSerializedSize (void) const override
  {
    return 8;
  }

  virtual void Serialize (TagBuffer i) const override
  {
    i.WriteU64 (m_time);
  }

  virtual void Deserialize (TagBuffer i) override
  {
    m_time = i.ReadU64 ();
  }

  virtual void Print (std::ostream &os) const override
  {
    os << "t=" << m_time;
  }

  void SetTime (Time t)
  {
    m_time = (uint64_t) t.GetNanoSeconds ();
  }

  Time GetTime () const
  {
    return NanoSeconds (m_time);
  }

private:
  uint64_t m_time {0};
};

// ---------------------------------------------------------------------
// Simple NoC header: srcId, dstId, hop count
// ---------------------------------------------------------------------

class NoCHeader : public Header
{
public:
  static TypeId GetTypeId (void)
  {
    static TypeId tid = TypeId ("ns3::NoCHeader")
      .SetParent<Header> ()
      .SetGroupName ("NoC")
      .AddConstructor<NoCHeader> ();
    return tid;
  }

  virtual TypeId GetInstanceTypeId (void) const override
  {
    return GetTypeId ();
  }

  NoCHeader ()
    : m_src (0),
      m_dst (0),
      m_hops (0)
  {
  }

  void SetSrc (uint32_t s) { m_src = s; }
  void SetDst (uint32_t d) { m_dst = d; }
  void SetHops (uint32_t h) { m_hops = h; }
  void IncrementHops () { ++m_hops; }

  uint32_t GetSrc () const { return m_src; }
  uint32_t GetDst () const { return m_dst; }
  uint32_t GetHops () const { return m_hops; }

  virtual uint32_t GetSerializedSize (void) const override
  {
    return 12; // 3 * uint32_t
  }

  virtual void Serialize (Buffer::Iterator start) const override
  {
    start.WriteU32 (m_src);
    start.WriteU32 (m_dst);
    start.WriteU32 (m_hops);
  }

  virtual uint32_t Deserialize (Buffer::Iterator start) override
  {
    m_src  = start.ReadU32 ();
    m_dst  = start.ReadU32 ();
    m_hops = start.ReadU32 ();
    return GetSerializedSize ();
  }

  virtual void Print (std::ostream &os) const override
  {
    os << "NoCHeader(src=" << m_src
       << ", dst=" << m_dst
       << ", hops=" << m_hops << ")";
  }

private:
  uint32_t m_src;
  uint32_t m_dst;
  uint32_t m_hops;
};

// ---------------------------------------------------------------------
// Global metric variables (for APL & throughput)
// ---------------------------------------------------------------------

// NoC parameters, matching Tang et al.:
static const uint32_t g_flitsPerPacket = 8;                // len = 8 flits
static Time           g_cycleTime      = NanoSeconds (1);  // 1 cycle = 1 ns

// Measurement window start (after warm-up)
static Time g_measureStart = NanoSeconds (0);

// Accumulators
static uint64_t g_totalReceivedPackets   = 0;   // K in the paper
static double   g_sumPacketLatencyCycles = 0.0; // sum(lat_i) in cycles

// ---------------------------------------------------------------------
// Routing-pressure (φ) helpers
// ---------------------------------------------------------------------

enum MetricRouting
{
  METRIC_ROUTING_XY,
  METRIC_ROUTING_YX,
  METRIC_ROUTING_OE,
  METRIC_ROUTING_NF
};

enum MetricDir
{
  DIR_NONE = 0,
  DIR_E    = 1,
  DIR_W    = 2,
  DIR_N    = 3,
  DIR_S    = 4
};

// XY: dimension-ordered, X then Y
static bool
IsMoveAllowedXY (Coord cur,
                 MetricDir next,
                 int dx,
                 int dy)
{
  if (dx > 0)
    return next == DIR_E;
  if (dx < 0)
    return next == DIR_W;

  if (dy > 0)
    return next == DIR_S;
  if (dy < 0)
    return next == DIR_N;

  return false; // already at dest
}

// YX: dimension-ordered, Y then X
static bool
IsMoveAllowedYX (Coord cur,
                 MetricDir next,
                 int dx,
                 int dy)
{
  if (dy > 0)
    return next == DIR_S;
  if (dy < 0)
    return next == DIR_N;

  if (dx > 0)
    return next == DIR_E;
  if (dx < 0)
    return next == DIR_W;

  return false;
}

// Odd–Even turn model (Chiu 2000):
// - In even columns: forbid EN and ES (prev E, next N/S)
// - In odd columns:  forbid NW and SW (prev N/S, next W)
static bool
IsMoveAllowedOE (Coord cur,
                 MetricDir prev,
                 MetricDir next)
{
  if (prev == DIR_NONE)
    {
      // First hop unrestricted
      return true;
    }

  bool evenCol = ((cur.x % 2u) == 0u);

  if (evenCol)
    {
      if (prev == DIR_E && (next == DIR_N || next == DIR_S))
        return false;
    }
  else
    {
      if ((prev == DIR_N || prev == DIR_S) && next == DIR_W)
        return false;
    }

  return true;
}

// Negative-First turn model (Glass & Ni):
// Forbid NW (N->W) and ES (E->S) turns.
static bool
IsMoveAllowedNF (MetricDir prev,
                 MetricDir next)
{
  if (prev == DIR_N && next == DIR_W)
    return false; // NW
  if (prev == DIR_E && next == DIR_S)
    return false; // ES
  return true;
}

// Wrapper: is move from cur with (prevDir -> nextDir) allowed?
static bool
IsMoveAllowed (MetricRouting algo,
               Coord cur,
               MetricDir prev,
               MetricDir next,
               int dx,
               int dy)
{
  switch (algo)
    {
    case METRIC_ROUTING_XY:
      return IsMoveAllowedXY (cur, next, dx, dy);

    case METRIC_ROUTING_YX:
      return IsMoveAllowedYX (cur, next, dx, dy);

    case METRIC_ROUTING_OE:
      return IsMoveAllowedOE (cur, prev, next);

    case METRIC_ROUTING_NF:
      return IsMoveAllowedNF (prev, next);

    default:
      return true;
    }
}

// DFS enumeration of all minimal paths under given routing rules
static void
EnumeratePathsRec (uint32_t width,
                   uint32_t height,
                   uint32_t dstIdx,
                   MetricRouting algo,
                   uint32_t curIdx,
                   MetricDir prevDir,
                   std::vector<uint32_t> &curPath,
                   std::vector<std::vector<uint32_t>> &paths)
{
  if (curIdx == dstIdx)
    {
      paths.push_back (curPath);
      return;
    }

  Coord cur = IdxToCoord (curIdx, width);
  Coord dst = IdxToCoord (dstIdx, width);

  int dx = int (dst.x) - int (cur.x);
  int dy = int (dst.y) - int (cur.y);

  // Candidate minimal directions
  std::vector<MetricDir> cand;
  if (dx > 0)
    cand.push_back (DIR_E);
  else if (dx < 0)
    cand.push_back (DIR_W);

  if (dy > 0)
    cand.push_back (DIR_S);
  else if (dy < 0)
    cand.push_back (DIR_N);

  for (MetricDir next : cand)
    {
      if (!IsMoveAllowed (algo, cur, prevDir, next, dx, dy))
        continue;

      Coord nxt = MoveOneStep (cur, (int) next);
      if (!InBounds (nxt, width, height))
        continue;

      uint32_t nxtIdx = CoordToIdx (nxt.x, nxt.y, width);

      curPath.push_back (nxtIdx);
      EnumeratePathsRec (width,
                         height,
                         dstIdx,
                         algo,
                         nxtIdx,
                         next,
                         curPath,
                         paths);
      curPath.pop_back ();
    }
}

static std::vector<std::vector<uint32_t>>
EnumeratePaths (uint32_t width,
                uint32_t height,
                uint32_t srcIdx,
                uint32_t dstIdx,
                MetricRouting algo)
{
  std::vector<std::vector<uint32_t>> paths;
  std::vector<uint32_t> cur;
  cur.push_back (srcIdx);
  EnumeratePathsRec (width,
                     height,
                     dstIdx,
                     algo,
                     srcIdx,
                     DIR_NONE,
                     cur,
                     paths);
  return paths;
}

// Compute φ for a given mesh, traffic pattern, and routing algorithm
static double
ComputeRoutingPressurePhi (uint32_t width,
                           uint32_t height,
                           const std::string &traffic,
                           MetricRouting algo)
{
  uint32_t numNodes = width * height;

  using Edge = std::pair<uint32_t, uint32_t>;
  std::map<Edge, double> phiCh; // Σ_i (k_i / p_i) for each channel

  auto processPair = [&](uint32_t src, uint32_t dst)
  {
    if (src == dst)
      return;

    auto paths = EnumeratePaths (width, height, src, dst, algo);
    if (paths.empty ())
      return;

    double p_i = double (paths.size ());

    std::map<Edge, uint32_t> edgeCount;

    for (const auto &path : paths)
      {
        for (size_t k = 0; k + 1 < path.size (); ++k)
          {
            Edge e (path[k], path[k + 1]);
            edgeCount[e]++;
          }
      }

    for (const auto &kv : edgeCount)
      {
        double rho_i = double (kv.second) / p_i;
        phiCh[kv.first] += rho_i;
      }
  };

  for (uint32_t s = 0; s < numNodes; ++s)
    {
      Coord sc = IdxToCoord (s, width);

      if (traffic == "uniform")
        {
          for (uint32_t d = 0; d < numNodes; ++d)
            {
              if (d == s)
                continue;
              processPair (s, d);
            }
        }
      else if (traffic == "transpose1")
        {
          Coord dc;
          dc.x = width  - 1 - sc.y;
          dc.y = height - 1 - sc.x;
          uint32_t d = CoordToIdx (dc.x, dc.y, width);
          if (d != s)
            processPair (s, d);
        }
      else if (traffic == "transpose2")
        {
          if (width != height)
            continue; // assume square mesh only
          Coord dc;
          dc.x = sc.y;
          dc.y = sc.x;
          uint32_t d = CoordToIdx (dc.x, dc.y, width);
          if (d != s)
            processPair (s, d);
        }
      else
        {
          // unknown pattern
        }
    }

  double phi = 0.0;
  for (const auto &kv : phiCh)
    {
      if (kv.second > phi)
        phi = kv.second;
    }
  return phi;
}

// ---------------------------------------------------------------------
// NoC router application (actual simulation)
// ---------------------------------------------------------------------

class NoCRouterApp : public Application
{
public:
  NoCRouterApp ();
  virtual ~NoCRouterApp ();

  static TypeId GetTypeId (void);

  void Configure (uint32_t nodeId,
                  uint32_t width,
                  uint32_t height,
                  const std::string &routing,
                  double pir,
                  double packetRate,
                  uint32_t packetSizeBytes,
                  const std::vector<uint32_t> &dests);

  void AddPort (uint32_t neighborId, Ptr<NetDevice> dev);

private:
  struct NeighborPort
  {
    uint32_t       neighborId;
    Ptr<NetDevice> device;
  };

  struct Candidate
  {
    NeighborPort *port;
    MetricDir     dir;
  };

  virtual void StartApplication () override;
  virtual void StopApplication () override;

  void ScheduleNextInjection ();
  void InjectPacket ();

  bool ReceiveFromDevice (Ptr<NetDevice> dev,
                          Ptr<const Packet> packet,
                          uint16_t protocol,
                          const Address &src);

  void ForwardPacket (Ptr<Packet> pkt, uint32_t dstId, MetricDir prevDir);

  bool SelectNextHop (uint32_t dstId,
                      MetricDir prevDir,
                      Ptr<NetDevice> &outDev,
                      MetricDir &outDir);

  bool SelectNextHopXY (const std::vector<Candidate> &cands,
                        const Coord &cur,
                        const Coord &dst,
                        Ptr<NetDevice> &outDev,
                        MetricDir &outDir);

  bool SelectNextHopYX (const std::vector<Candidate> &cands,
                        const Coord &cur,
                        const Coord &dst,
                        Ptr<NetDevice> &outDev,
                        MetricDir &outDir);

  bool SelectNextHopOE (const std::vector<Candidate> &cands,
                        const Coord &cur,
                        MetricDir prevDir,
                        Ptr<NetDevice> &outDev,
                        MetricDir &outDir);

  bool SelectNextHopNF (const std::vector<Candidate> &cands,
                        MetricDir prevDir,
                        Ptr<NetDevice> &outDev,
                        MetricDir &outDir);

  // Config
  uint32_t          m_id {0};
  uint32_t          m_width {0};
  uint32_t          m_height {0};
  std::string       m_routing;
  double            m_pir {0.0};
  double            m_packetRate {0.0};
  uint32_t          m_packetSize {0};
  std::vector<uint32_t> m_dests;

  // Ports
  std::vector<NeighborPort> m_ports;

  // State
  bool              m_running {false};
  EventId           m_injectEvent;

  Ptr<ExponentialRandomVariable> m_interArrivalRv;
  Ptr<UniformRandomVariable>     m_destRv;
  Ptr<UniformRandomVariable>     m_randRv;
};

TypeId
NoCRouterApp::GetTypeId (void)
{
  static TypeId tid = TypeId ("ns3::NoCRouterApp")
    .SetParent<Application> ()
    .SetGroupName ("NoC")
    .AddConstructor<NoCRouterApp> ();
  return tid;
}

NoCRouterApp::NoCRouterApp () {}
NoCRouterApp::~NoCRouterApp () { m_ports.clear (); }

void
NoCRouterApp::Configure (uint32_t nodeId,
                         uint32_t width,
                         uint32_t height,
                         const std::string &routing,
                         double pir,
                         double packetRate,
                         uint32_t packetSizeBytes,
                         const std::vector<uint32_t> &dests)
{
  m_id         = nodeId;
  m_width      = width;
  m_height     = height;
  m_routing    = routing;
  m_pir        = pir;
  m_packetRate = packetRate;
  m_packetSize = packetSizeBytes;
  m_dests      = dests;

  m_interArrivalRv = CreateObject<ExponentialRandomVariable> ();
  if (m_packetRate > 0.0)
    {
      double mean = 1.0 / m_packetRate; // seconds
      m_interArrivalRv->SetAttribute ("Mean", DoubleValue (mean));
    }
  else
    {
      m_interArrivalRv->SetAttribute ("Mean", DoubleValue (1e9));
    }

  m_destRv = CreateObject<UniformRandomVariable> ();
  m_randRv = CreateObject<UniformRandomVariable> ();
}

void
NoCRouterApp::AddPort (uint32_t neighborId, Ptr<NetDevice> dev)
{
  NeighborPort p;
  p.neighborId = neighborId;
  p.device     = dev;
  m_ports.push_back (p);
}

void
NoCRouterApp::StartApplication ()
{
  m_running = true;

  for (auto &p : m_ports)
    {
      p.device->SetReceiveCallback (
        MakeCallback (&NoCRouterApp::ReceiveFromDevice, this));
    }

  if (!m_dests.empty () && m_packetRate > 0.0)
    {
      ScheduleNextInjection ();
    }
}

void
NoCRouterApp::StopApplication ()
{
  m_running = false;

  if (m_injectEvent.IsPending ())
    {
      Simulator::Cancel (m_injectEvent);
    }
}

void
NoCRouterApp::ScheduleNextInjection ()
{
  if (!m_running || m_dests.empty () || m_packetRate <= 0.0)
    {
      return;
    }

  double nextInterval = m_interArrivalRv->GetValue (); // seconds
  Time tNext = Seconds (nextInterval);
  m_injectEvent = Simulator::Schedule (tNext, &NoCRouterApp::InjectPacket, this);
}

void
NoCRouterApp::InjectPacket ()
{
  if (!m_running || m_dests.empty ())
    {
      return;
    }

  uint32_t idx = m_destRv->GetInteger (0, (int) m_dests.size () - 1);
  uint32_t dstId = m_dests[idx];

  Ptr<Packet> pkt = Create<Packet> (m_packetSize);

  SendTimeTag tag;
  tag.SetTime (Simulator::Now ());
  pkt->AddPacketTag (tag);

  NoCHeader hdr;
  hdr.SetSrc (m_id);
  hdr.SetDst (dstId);
  hdr.SetHops (0);
  pkt->AddHeader (hdr);

  // First hop has no previous direction
  ForwardPacket (pkt, dstId, DIR_NONE);

  ScheduleNextInjection ();
}

bool
NoCRouterApp::ReceiveFromDevice (Ptr<NetDevice> dev,
                                 Ptr<const Packet> packet,
                                 uint16_t protocol,
                                 const Address &src)
{
  if (!m_running)
    {
      return false;
    }

  Ptr<Packet> pkt = packet->Copy ();

  NoCHeader hdr;
  bool ok = pkt->RemoveHeader (hdr);
  if (!ok)
    {
      return false;
    }

  uint32_t dstId = hdr.GetDst ();

  if (dstId == m_id)
    {
      // Reached destination
      SendTimeTag tag;
      bool found = pkt->PeekPacketTag (tag);
      if (found)
        {
          Time now = Simulator::Now ();
          if (now >= g_measureStart)
            {
              Time latency = now - tag.GetTime ();
              double latencyCycles =
                (double) latency.GetNanoSeconds () /
                (double) g_cycleTime.GetNanoSeconds ();

              g_totalReceivedPackets++;
              g_sumPacketLatencyCycles += latencyCycles;
            }
        }
      return true;
    }

  // Determine previous direction from incoming device
  MetricDir prevDir = DIR_NONE;
  uint32_t  fromId  = m_id; // default

  for (const auto &p : m_ports)
    {
      if (p.device == dev)
        {
          fromId = p.neighborId;
          break;
        }
    }

  Coord cur  = IdxToCoord (m_id,   m_width);
  Coord from = IdxToCoord (fromId, m_width);

  if (from.x + 1 == cur.x && from.y == cur.y) prevDir = DIR_E;
  else if (from.x == cur.x + 1 && from.y == cur.y) prevDir = DIR_W;
  else if (from.y + 1 == cur.y && from.x == cur.x) prevDir = DIR_S;
  else if (from.y == cur.y + 1 && from.x == cur.x) prevDir = DIR_N;
  else prevDir = DIR_NONE;

  hdr.IncrementHops ();
  pkt->AddHeader (hdr);

  ForwardPacket (pkt, dstId, prevDir);

  return true;
}

void
NoCRouterApp::ForwardPacket (Ptr<Packet> pkt, uint32_t dstId, MetricDir prevDir)
{
  Ptr<NetDevice> outDev;
  MetricDir outDir = DIR_E;

  bool ok = SelectNextHop (dstId, prevDir, outDev, outDir);
  if (!ok || outDev == nullptr)
    {
      return;
    }

  Address dst = outDev->GetBroadcast ();
  outDev->Send (pkt, dst, 0x0800);
}

bool
NoCRouterApp::SelectNextHop (uint32_t dstId,
                             MetricDir prevDir,
                             Ptr<NetDevice> &outDev,
                             MetricDir &outDir)
{
  Coord cur = IdxToCoord (m_id, m_width);
  Coord dst = IdxToCoord (dstId, m_width);

  int dx0 = int (dst.x) - int (cur.x);
  int dy0 = int (dst.y) - int (cur.y);
  int dist0 = std::abs (dx0) + std::abs (dy0);

  if (dist0 == 0)
    {
      outDev = nullptr;
      return false;
    }

  // Collect all *minimal* neighbor moves
  std::vector<Candidate> cands;

  for (auto &p : m_ports)
    {
      Coord nb = IdxToCoord (p.neighborId, m_width);

      int dx1 = int (dst.x) - int (nb.x);
      int dy1 = int (dst.y) - int (nb.y);
      int dist1 = std::abs (dx1) + std::abs (dy1);

      if (dist1 >= dist0)
        continue;

      MetricDir dir = DIR_NONE;
      if (nb.x == cur.x + 1 && nb.y == cur.y) dir = DIR_E;
      else if (nb.x + 1 == cur.x && nb.y == cur.y) dir = DIR_W;
      else if (nb.y == cur.y + 1 && nb.x == cur.x) dir = DIR_S;
      else if (nb.y + 1 == cur.y && nb.x == cur.x) dir = DIR_N;

      if (dir == DIR_NONE)
        continue;

      Candidate c;
      c.port = &p;
      c.dir  = dir;
      cands.push_back (c);
    }

  if (cands.empty ())
    {
      outDev = nullptr;
      return false;
    }

  bool ok = false;

  if (m_routing == "xy")
    {
      ok = SelectNextHopXY (cands, cur, dst, outDev, outDir);
    }
  else if (m_routing == "yx")
    {
      ok = SelectNextHopYX (cands, cur, dst, outDev, outDir);
    }
  else if (m_routing == "oe")
    {
      ok = SelectNextHopOE (cands, cur, prevDir, outDev, outDir);
    }
  else if (m_routing == "nf")
    {
      ok = SelectNextHopNF (cands, prevDir, outDev, outDir);
    }
  else
    {
      // default to OE if unknown
      ok = SelectNextHopOE (cands, cur, prevDir, outDev, outDir);
    }

  return ok;
}

// strict XY: X dimension first, then Y
bool
NoCRouterApp::SelectNextHopXY (const std::vector<Candidate> &cands,
                               const Coord &cur,
                               const Coord &dst,
                               Ptr<NetDevice> &outDev,
                               MetricDir &outDir)
{
  MetricDir needed = DIR_NONE;

  if (cur.x != dst.x)
    {
      if (dst.x > cur.x) needed = DIR_E;
      else needed = DIR_W;
    }
  else
    {
      if (dst.y > cur.y) needed = DIR_S;
      else needed = DIR_N;
    }

  for (const auto &c : cands)
    {
      if (c.dir == needed)
        {
          outDev = c.port->device;
          outDir = c.dir;
          return true;
        }
    }

  // Should not happen, but fall back just in case
  outDev = cands.front ().port->device;
  outDir = cands.front ().dir;
  return true;
}

// strict YX: Y dimension first, then X
bool
NoCRouterApp::SelectNextHopYX (const std::vector<Candidate> &cands,
                               const Coord &cur,
                               const Coord &dst,
                               Ptr<NetDevice> &outDev,
                               MetricDir &outDir)
{
  MetricDir needed = DIR_NONE;

  if (cur.y != dst.y)
    {
      if (dst.y > cur.y) needed = DIR_S;
      else needed = DIR_N;
    }
  else
    {
      if (dst.x > cur.x) needed = DIR_E;
      else needed = DIR_W;
    }

  for (const auto &c : cands)
    {
      if (c.dir == needed)
        {
          outDev = c.port->device;
          outDir = c.dir;
          return true;
        }
    }

  outDev = cands.front ().port->device;
  outDir = cands.front ().dir;
  return true;
}

// OE: partial adaptive, enforce OE turn rules and choose randomly among allowed minimal directions.
bool
NoCRouterApp::SelectNextHopOE (const std::vector<Candidate> &cands,
                               const Coord &cur,
                               MetricDir prevDir,
                               Ptr<NetDevice> &outDev,
                               MetricDir &outDir)
{
  std::vector<const Candidate*> allowed;

  for (const auto &c : cands)
    {
      if (IsMoveAllowedOE (cur, prevDir, c.dir))
        {
          allowed.push_back (&c);
        }
    }

  if (allowed.empty ())
    {
      // Should not happen, but if it does, ignore the turn rules to avoid deadlock in the sim.
      allowed.reserve (cands.size ());
      for (const auto &c : cands) allowed.push_back (&c);
    }

  const Candidate *chosen = nullptr;
  if (allowed.size () == 1)
    {
      chosen = allowed[0];
    }
  else
    {
      uint32_t idx = m_randRv->GetInteger (0, (int) allowed.size () - 1);
      chosen = allowed[idx];
    }

  outDev = chosen->port->device;
  outDir = chosen->dir;
  return true;
}

// NF: partial adaptive, enforce NF turn rules and prefer negative directions (W,N).
bool
NoCRouterApp::SelectNextHopNF (const std::vector<Candidate> &cands,
                               MetricDir prevDir,
                               Ptr<NetDevice> &outDev,
                               MetricDir &outDir)
{
  std::vector<const Candidate*> allowed;
  for (const auto &c : cands)
    {
      if (IsMoveAllowedNF (prevDir, c.dir))
        {
          allowed.push_back (&c);
        }
    }

  if (allowed.empty ())
    {
      // Should not happen; fall back to ignoring turn rules.
      allowed.reserve (cands.size ());
      for (const auto &c : cands) allowed.push_back (&c);
    }

  std::vector<const Candidate*> neg;
  std::vector<const Candidate*> pos;

  for (const auto *c : allowed)
    {
      if (c->dir == DIR_W || c->dir == DIR_N)
        neg.push_back (c);
      else
        pos.push_back (c);
    }

  const Candidate *chosen = nullptr;
  if (!neg.empty ())
    {
      uint32_t idx = m_randRv->GetInteger (0, (int) neg.size () - 1);
      chosen = neg[idx];
    }
  else
    {
      uint32_t idx = m_randRv->GetInteger (0, (int) pos.size () - 1);
      chosen = pos[idx];
    }

  outDev = chosen->port->device;
  outDir = chosen->dir;
  return true;
}

// ---------------------------------------------------------------------
// main() – build mesh, run traffic, compute metrics + φ
// ---------------------------------------------------------------------

int
main (int argc, char *argv[])
{
  uint32_t width         = 7;
  uint32_t height        = 7;
  std::string dataRate   = "16Gbps";
  std::string delay      = "0ns";
  double pir             = 0.01;       // packets per node per cycle
  uint32_t warmupCycles  = 1000;
  uint32_t measureCycles = 20000;
  uint32_t packetSize    = 32;         // bytes
  std::string traffic    = "uniform";  // uniform | transpose1 | transpose2
  std::string routing    = "xy";       // xy | yx | oe | nf

  CommandLine cmd;
  cmd.AddValue ("width",         "Mesh width (columns, X dimension)", width);
  cmd.AddValue ("height",        "Mesh height (rows, Y dimension)",   height);
  cmd.AddValue ("dataRate",      "Point-to-Point link data rate",     dataRate);
  cmd.AddValue ("delay",         "Point-to-Point link delay",         delay);
  cmd.AddValue ("pir",           "Packet injection rate per node per cycle", pir);
  cmd.AddValue ("warmup",        "Warm-up cycles",                    warmupCycles);
  cmd.AddValue ("measure",       "Measured cycles",                   measureCycles);
  cmd.AddValue ("packetSize",    "Packet size in bytes",              packetSize);
  cmd.AddValue ("traffic",       "Traffic pattern: uniform|transpose1|transpose2", traffic);
  cmd.AddValue ("routing",       "Routing algorithm: xy|yx|oe|nf", routing);
  cmd.Parse (argc, argv);

  uint32_t numNodes = width * height;

  if (traffic != "uniform" && width != height)
    {
      NS_FATAL_ERROR ("Transpose traffic assumes a square mesh");
    }

  for (auto &ch : routing)
    {
      ch = std::tolower (ch);
    }

  NS_LOG_UNCOND ("Mesh " << width << "x" << height
                 << ", nodes=" << numNodes
                 << ", PIR=" << pir
                 << ", warmup=" << warmupCycles
                 << ", measure=" << measureCycles
                 << ", traffic=" << traffic
                 << ", routing=" << routing
                 << ", dataRate=" << dataRate
                 << ", delay=" << delay);

  Time totalSimTime = NanoSeconds ( (uint64_t) (warmupCycles + measureCycles) );
  g_measureStart    = NanoSeconds ( (uint64_t) warmupCycles );

  double cycleSeconds = g_cycleTime.GetSeconds ();
  double packetRate   = pir / cycleSeconds;   // packets / node / second

  // ------------------------ Compute φ (routing pressure) ------------------------

  MetricRouting metricAlgo = METRIC_ROUTING_XY;
  if (routing == "xy")
    metricAlgo = METRIC_ROUTING_XY;
  else if (routing == "yx")
    metricAlgo = METRIC_ROUTING_YX;
  else if (routing == "oe")
    metricAlgo = METRIC_ROUTING_OE;
  else if (routing == "nf")
    metricAlgo = METRIC_ROUTING_NF;

  double phi = ComputeRoutingPressurePhi (width, height, traffic, metricAlgo);

  // Known φ values from Tang et al. (for comparison only)
  double phiFromPaper = 0.0;
  if (width == 7 && height == 7)
    {
      if (traffic == "transpose1")
        {
          if (routing == "xy") phiFromPaper = 6.0;
          else if (routing == "oe") phiFromPaper = 4.81;
          else if (routing == "nf") phiFromPaper = 6.0;
        }
      else if (traffic == "transpose2")
        {
          if (routing == "xy") phiFromPaper = 6.0;
          else if (routing == "oe") phiFromPaper = 4.81;
          else if (routing == "nf") phiFromPaper = 2.41;
        }
    }

  // ------------------------ Create nodes & links ------------------------

  NodeContainer nodes;
  nodes.Create (numNodes);

  PointToPointHelper p2p;
  p2p.SetDeviceAttribute ("DataRate", StringValue (dataRate));
  p2p.SetChannelAttribute ("Delay",   StringValue (delay));
  p2p.SetQueue ("ns3::DropTailQueue<Packet>",
                "MaxSize", StringValue ("100000p"));

  typedef std::pair<uint32_t, Ptr<NetDevice>> NeighborInfo;
  std::vector<std::vector<NeighborInfo>> adj (numNodes);

  // Horizontal links
  for (uint32_t y = 0; y < height; ++y)
    {
      for (uint32_t x = 0; x + 1 < width; ++x)
        {
          uint32_t from = CoordToIdx (x,     y, width);
          uint32_t to   = CoordToIdx (x + 1, y, width);

          NetDeviceContainer nd = p2p.Install (nodes.Get (from), nodes.Get (to));
          Ptr<NetDevice> devFrom = nd.Get (0);
          Ptr<NetDevice> devTo   = nd.Get (1);

          adj[from].push_back (NeighborInfo (to, devFrom));
          adj[to].push_back   (NeighborInfo (from, devTo));
        }
    }

  // Vertical links
  for (uint32_t y = 0; y + 1 < height; ++y)
    {
      for (uint32_t x = 0; x < width; ++x)
        {
          uint32_t from = CoordToIdx (x, y,     width);
          uint32_t to   = CoordToIdx (x, y + 1, width);

          NetDeviceContainer nd = p2p.Install (nodes.Get (from), nodes.Get (to));
          Ptr<NetDevice> devFrom = nd.Get (0);
          Ptr<NetDevice> devTo   = nd.Get (1);

          adj[from].push_back (NeighborInfo (to, devFrom));
          adj[to].push_back   (NeighborInfo (from, devTo));
        }
    }

  // ------------------------ Node positions for NetAnim ------------------------

  MobilityHelper mobility;
  Ptr<ListPositionAllocator> pos = CreateObject<ListPositionAllocator> ();

  double step = 50.0;
  for (uint32_t y = 0; y < height; ++y)
    {
      for (uint32_t x = 0; x < width; ++x)
        {
          pos->Add (Vector (x * step, y * step, 0.0));
        }
    }

  mobility.SetPositionAllocator (pos);
  mobility.SetMobilityModel ("ns3::ConstantPositionMobilityModel");
  mobility.Install (nodes);

  AnimationInterface anim ("noc-topology.xml");
  for (uint32_t i = 0; i < numNodes; ++i)
    {
      Coord c = IdxToCoord (i, width);
      std::ostringstream oss;
      oss << i << " (" << c.x << "," << c.y << ")";
      anim.UpdateNodeDescription (i, oss.str ());
      anim.UpdateNodeColor (i, 0, 255, 0);
    }

  // ------------------------ Build destination sets for injection ---------

  std::vector<std::vector<uint32_t>> dests (numNodes);

  if (traffic == "uniform")
    {
      for (uint32_t i = 0; i < numNodes; ++i)
        {
          for (uint32_t j = 0; j < numNodes; ++j)
            {
              if (i == j) continue;
              dests[i].push_back (j);
            }
        }
    }
  else if (traffic == "transpose1")
    {
      uint32_t N = width;
      for (uint32_t i = 0; i < numNodes; ++i)
        {
          Coord src = IdxToCoord (i, width);
          uint32_t dstX = (N - 1) - src.y;
          uint32_t dstY = (N - 1) - src.x;
          uint32_t dstId = CoordToIdx (dstX, dstY, width);
          if (dstId == i)
            dstId = (i + width) % numNodes;
          dests[i].push_back (dstId);
        }
    }
  else if (traffic == "transpose2")
    {
      for (uint32_t i = 0; i < numNodes; ++i)
        {
          Coord src = IdxToCoord (i, width);
          uint32_t dstX = src.y;
          uint32_t dstY = src.x;
          uint32_t dstId = CoordToIdx (dstX, dstY, width);
          if (dstId == i)
            dstId = (i + 1) % numNodes;
          dests[i].push_back (dstId);
        }
    }
  else
    {
      NS_FATAL_ERROR ("Unknown traffic pattern " << traffic);
    }

  // ------------------------ Install router apps ------------------------

  for (uint32_t i = 0; i < numNodes; ++i)
    {
      Ptr<NoCRouterApp> app = CreateObject<NoCRouterApp> ();
      app->Configure (i, width, height, routing, pir,
                      packetRate, packetSize, dests[i]);

      for (const auto &nbr : adj[i])
        {
          app->AddPort (nbr.first, nbr.second);
        }

      nodes.Get (i)->AddApplication (app);
      app->SetStartTime (Seconds (0.0));
      app->SetStopTime (totalSimTime);
    }

  // ------------------------ Run simulation ------------------------

  Simulator::Stop (totalSimTime);
  Simulator::Run ();
  Simulator::Destroy ();

  // ------------------------ Metrics ------------------------

  double K = (double) g_totalReceivedPackets;
  if (K == 0)
    {
      std::cout << "No packets received during measuring window.\n";
      return 0;
    }

  double avgLatencyCycles = g_sumPacketLatencyCycles / K;

  double totalCyclesMeasure = (double) measureCycles;
  double totalFlits         = (double) g_flitsPerPacket * (double) g_totalReceivedPackets;
  double throughput         = totalFlits / ( (double) numNodes * totalCyclesMeasure );

  std::cout << "======== Simulation Results ========\n";
  std::cout << "Nodes:                 " << numNodes << "\n";
  std::cout << "PIR (per node/cycle):  " << pir << "\n";
  std::cout << "Warm-up cycles:        " << warmupCycles << "\n";
  std::cout << "Measured cycles:       " << measureCycles << "\n";
  std::cout << "Traffic pattern:       " << traffic << "\n";
  std::cout << "Routing algorithm:     " << routing << "\n";
  std::cout << "Received packets (K):  " << g_totalReceivedPackets << "\n";
  std::cout << "Avg packet latency:    " << avgLatencyCycles << " cycles\n";
  std::cout << "Throughput:            " << throughput
            << " flits / (node * cycle)\n";

  // φ-based bound:
  double frate = 0.5;                 // flits/cycle
  double len   = (double) g_flitsPerPacket; // flits/packet
  double pirMax = (phi > 0.0) ? ((frate / len) / phi) : 0.0;

  std::cout << "------ Routing-pressure bound ------\n";
  std::cout << "phi (computed):        " << phi << "\n";
  if (phiFromPaper > 0.0)
    {
      std::cout << "phi (from paper, if known): " << phiFromPaper << "\n";
    }
  std::cout << "PIR_max (bound):       " << pirMax << "\n";
  if (pirMax > 0.0)
    {
      std::cout << "PIR / PIR_max:         " << (pir / pirMax) << "\n";
    }
  std::cout << "------------------------------------\n";
  std::cout << "====================================\n";

  return 0;
}

