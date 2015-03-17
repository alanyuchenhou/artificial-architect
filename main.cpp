
// Tree Based Topology Flit Level Wormhole Simulator
// Skeleton by Michael Jones, UBC
// Code cleanup and additions by Brett Feero, WSU
// 
#include<cstdlib>
#include<cassert>
#include <stdexcept>
#include <stdio.h>
#include <iostream>
#include <fstream>
#include <string>
#include <math.h>
#include <cmath>
//#include <conio.h>
#include <time.h>
#include "port.h"
#include "ip.h"
#include "msg.h"
#include "header.h"
#include "CmdLine.h"

#define BFT 0
#define RING 1
#define OCTO 2
#define OCTO5 3
#define OCTOM 4
#define OCTOM3 5
#define OCTOM256 6
#define KARY 7
#define MESH 8
#define TORUS 9
#define CUBE 10
#define HBUS 11
#define CLUSTERED 12
#define STACKED 13
#define SUPERS 14

#define POISSON 0
#define SS 1
#define SS_MULTIPLIER 0.37

using namespace std;
// GLOBAL VARIABLES ********************************

int wireless_usage = 0;
int rerouted = 0;
int total_wireless = 0;
int wireless_done = 0;
//start of mst stuff
#define MTREES 4
#define MST_N 64 //the number of switches in network
#define NUM_CORES 128 //the number of cores in network (should be same as MST_N)!
#define NUM_PATHS 15
#define NUM_WI_PATHS NUM_PATHS/2
#define ADDRESS_LENGTH 64 //max number of depth of the tree
#define WINDOW_SIZE 100 //DTM WINDOW, how often should we determine whether or not to re-route)
#define AVG_COMMDENSITY 0.1672 //average router communication densities, determined by profiling the benchmark
#define MAX_COMMDENSITY 0.063781 //maximum router communication densities, determined by profiling the benchmark
//canneal: max: 0.073 avg: 0.0272125
//fft: max: .121 avg: .043788
//lu: max: .148 avg: .043544
//radix: max: .1672 avg: .063781
#define BETA 1.0 //AVG_COMMDENSITY/2.0 //AVG < BETA < (AVG+MAX)/2
#define GLOBAL true
#define MAX_TOKEN_PACKETS 15

#define fMESH 0

#define NUM_IPS 64

int routerStages = 3;
int pathLengthRepeaters[NUM_IPS][NUM_IPS][2] = {0};
int pathLengthRepeatersWI[NUM_IPS][NUM_IPS] = {0};
int minPath = 0;
#if fMESH
#define fMROOTS false
#define fLASH false
#define fMPLASH false
#define fALASH false

#define fWIRELESS false
#define fPHYSICALDIST false

bool TOKEN_MAC=false;  //Token MAC
bool DC_MAC=false;    //distributed control MAC

bool fSTART=false;

#define fLATENCY true
#define fPOWER false

#define fUNIFORMDIST false
#define fVIRTDIST false
#define fPRIORITYLAYER false

#define VFI 0

#define HARD_RESET false
#define SOFT_RESET false
#else
#define fMROOTS false
#define fLASH false
#define fMPLASH false
#define fALASH true

bool TOKEN_MAC=false;  //Token MAC
bool DC_MAC=false;    //distributed control MAC

bool fSTART=true; //Start from beginning
#define fWIRELESS false
#define fPHYSICALDIST false

#define fLATENCY true
#define fPOWER false

#define fUNIFORMDIST false
#define fVIRTDIST false
#define fPRIORITYLAYER true

#define VFI 0

#define HARD_RESET false
#define SOFT_RESET true
#endif
#define fBENCHMARK true		// yuchen: traffic specification
bool fFFT = false;
bool fRADIX = false;
bool fLU = false;
bool fWATER = false;
bool fCANNEAL = false;
bool fFLUIDANIMATE = false;
bool fDEDUP = false;
bool fVIPS = false;
bool fBODYTRACK = false;
bool fcombined = false;
#define fDEDUP_wonje false
#define fFLUID_wonje  false
#define fVIPS_wonje false 

#define fSWAPTION false
#define fFREQMINE false
#define fRADIX10 false
#define fRADIX20 false
#define fRADIX30 false
#define fRADIX40 false
#define fRADIX50 false
#define fRADIX60 false
#define fRADIX70 false
#define fRADIX80 false
#define fRADIX90 false
#define fRADIX100 false
#define fBODYTRACK10 false
#define fBODYTRACK20 false
#define fBODYTRACK30 false
#define fBODYTRACK40 false
#define fBODYTRACK50 false
#define fBODYTRACK60 false
#define fBODYTRACK70 false
#define fBODYTRACK80 false
#define fBODYTRACK90 false
#define fBODYTRACK100 false
#define fCANNEAL10 false
#define fCANNEAL20 false
#define fCANNEAL30 false
#define fCANNEAL40 false
#define fCANNEAL50 false
#define fCANNEAL60 false
#define fCANNEAL70 false
#define fCANNEAL80 false
#define fCANNEAL90 false
#define fCANNEAL100 false

#define fWEIGHTED false
#define WEIGHT 2

#define fDVFS false

double averageLatency[100] = {0.0};
double averageLatency2[100] = {0.0};

int windowSize = 400;

int wirelessPathNum = 1;
int wirelessPathThreshold = 0;
int wiWaitThreshold = 0;

double **fijMatrix;
double *fijMatrixSum;
double fijAverage;
double fij50;
int** flits_between_switches;  //sourav

int messageVfiTotal[NUM_IPS][NUM_IPS][4];
int latencyPairs[NUM_IPS][NUM_IPS];
int messageTotal[NUM_IPS][NUM_IPS];

int messagesInjected[64][64];
int *** communicationPerLink;
int communicationTotal = 0;
int flitsInjected = 0;
int flitsConsumed = 0;
int flitsMoved = 0;
double maxLatency2 = 0;
typedef enum {
	None,
	Down,
	Up,
	WirelessShortcut,
	WirelineShortcut
} LinkTypes;

typedef enum {
	Wireline = 0,
	Wireless1,
	Wireless2,
	Wireless3
} Channels;

typedef struct RoutingTableEntry
{
	int NextRouter;
	LinkTypes LinkType;
	bool HasWirelessToken;
	Channels ChannelType;
	int DistanceFromFinalDestination[NUM_CORES];
	double ThrottlingRatio[NUM_CORES];
	int Rank[NUM_CORES];
} RoutingTableEntry;

typedef struct RoutingTable
{
	bool Throttled;
	int ThrottleAttempts;
	int *address[MTREES];
	int numLinks;
	RoutingTableEntry *Entries[MTREES];
	double commDensity;
}RoutingTable;

typedef struct paths
{
	int plength;
	int rank;
	int path[24];
	int layer;
}Paths;

int ppath[24] = {0};
int path_length = 0;
int ppp = 0;
int wirelessP = 0;
Paths mPath[NUM_CORES][NUM_CORES][MTREES][NUM_PATHS];

int pathLength1(int source, int dest, int tree_number);
void rankPaths(int tree_number);
void findPaths(int hop_count, int source, int current, int dest, int tree, LinkTypes prevLink);
int globalThermalRerout(int currentRouter, int sourceRouter, int destinationRouter, int *pathNumber, int tree_number);

RoutingTable RT[NUM_CORES];

char connections[NUM_CORES][NUM_CORES+1][MTREES];

int C[MST_N][MST_N]; //connections between switches
int UpTree[MST_N][MST_N][MTREES]; //nodes that can be accessed going 'up'
int DownTree[MST_N][MST_N][MTREES]; //nodes that can be accessed going 'down'
int V[MST_N][MTREES]; //force V to contain TreeRoot only
int L[MST_N][MTREES]; //1st level of the root
int D[MST_N][MTREES]; //number of daughters of each switch
int TreeRoot[MTREES] = {26, 2, 12, 4}; //root of mst tree
//paul 4 {0, 22, 51, 61}
//radix normal {26, 2, 12, 4}
//lu normal {31, 26, 12, 13}
//fft normal {26, 12, 2, 10}
//canneal normal {26, 2, 30, 12}
//best 4 {26, 18, 34, 32}
int SubTreeLabel[MTREES][MST_N][MST_N]; //max depth of MST_N

double benchmarkLoad[MST_N];
double FijMATRIX[MST_N][MST_N];
//end of mst stuff

//start of debug stuff
int link_flit_counter[2432];
int flitsPerLink[NUM_IPS][NUM_IPS];
int wirelessUsage[NUM_IPS] = {0};
int node_flit_counter[128];
int flit_hop_count;
int total_flit_count;
int doing_something = 0;
//Karthi Energy Declartions
double link_cartesian_distance[MST_N][MST_N];
int wireless_node[64];
int GATEWAY=36;

//Kartni MAC Declarations
bool free_token[3]={true};
bool token_request[128][3]={false};
int  last_token_node_index[3]={0};
int request_count[3]={0};
int count_possible_wireless_tx=0;
int net_possible_wireless_tx=0;
char path_filename[30];
char benchmark[10];
double traffic_const;

int token1 = 0;
int token2 = 0;
int token3 = 0;
int treeToken = 0;
//bool stallToken[3][MTREES];
int wirelesstaken = 0;
bool stallToken[3] = {false, false, false};
int tokenPacketCount[3] = {0, 0, 0};

#if VFI
//NUM_PORTS = 16

int channel_1_switch[5] = {0, 5, 18, 41, 45};
int channel_2_switch[4] = {0, 28, 54, 57};
int channel_3_switch[5] = {0, 12, 24, 36, 56};

int channel_1_nodes = 5;
int channel_2_nodes = 4;
int channel_3_nodes = 5;

int channel_1_node[5] = {64, 69, 82, 105, 109};
int channel_2_node[4] = {64, 92, 118, 121};
int channel_3_node[5] = {64, 76, 88, 100, 120};

int nextPortNumbers[64] = {1029,1043,1061,1075,1094,1107,1122,1139,1157,1172,1189,1203,1223,1235,1252,1267,1284,1303,1320,1333,1350,1364,1383,1397,1411,1427,1447,1463,1480,1495,1512,1524,1540,1558,1574,1591,1608,1624,1635,1651,1669,1683,1701,1715,1734,1752,1764,1778,1795,1813,1829,1848,1863,1877,1896,1908,1925,1941,1957,1970,1988,2006,2020,2038};
int tokenPortStart[64] = {1029,1043,1061,1075,1094,1107,1122,1139,1157,1172,1189,1203,1223,1235,1252,1267,1284,1303,1320,1333,1350,1364,1383,1397,1411,1427,1447,1463,1480,1495,1512,1524,1540,1558,1574,1591,1608,1624,1635,1651,1669,1683,1701,1715,1734,1752,1764,1778,1795,1813,1829,1848,1863,1877,1896,1908,1925,1941,1957,1970,1988,2006,2020,2038};

#else
int channel_1_switch[5] = {0, 4, 14, 36, 47};
int channel_2_switch[4] = {3, 23, 25, 36};
int channel_3_switch[5] = {8, 36, 49, 59, 63};

int channel_1_nodes = 5;
int channel_2_nodes = 4;
int channel_3_nodes = 5;

int channel_1_node[5] = {64, 68, 78, 100, 111};
int channel_2_node[4] = {67, 87, 89, 100};
int channel_3_node[5] = {72, 100, 113, 123, 127};

int nextPortNumbers[64] = {1094, 1109, 1129, 1142, 1163, 1176, 1193, 1211, 1231, 1246, 1263, 1279, 1296, 1313, 1332, 1346, 1364, 1379, 1402, 1418, 1435, 1449, 1467, 1484, 1498, 1521, 1537, 1552, 1569, 1585, 1606, 1620, 1638, 1654, 1674, 1687, 1706, 1720, 1737, 1754, 1773, 1790, 1805, 1821, 1843, 1860, 1875, 1894, 1909, 1928, 1941, 1957, 1979, 1994, 2010, 2027, 2043, 2060, 2078, 2097, 2116, 2127, 2146, 2164};
int tokenPortStart[64] = {1094, 1109, 1129, 1142, 1163, 1176, 1193, 1211, 1231, 1246, 1263, 1279, 1296, 1313, 1332, 1346, 1364, 1379, 1402, 1418, 1435, 1449, 1467, 1484, 1498, 1521, 1537, 1552, 1569, 1585, 1606, 1620, 1638, 1654, 1674, 1687, 1706, 1720, 1737, 1754, 1773, 1790, 1805, 1821, 1843, 1860, 1875, 1894, 1909, 1928, 1941, 1957, 1979, 1994, 2010, 2027, 2043, 2060, 2078, 2097, 2116, 2127, 2146, 2164};

#endif

ifstream random_number_file("random.txt");
int random_number_count = 0;
//end of debug stuff

int numLayers = 4;
int maxPaths = 5;
int maxPathLength = 20;
int **** MultiPathMsg; //Source Dest PathNumber Node#
int *** MultiPathLength; //Source Dest PathNumber
int ** MultiPathTotal; //Source Dest
int *** pathAddr;
int *** pathLayer;
double ** nodeUsage;
int * numPerLayer;
int **** dependencyLayer;
int **** dependencyCannot;
int **** pathAllocLayer; //ALASH Layers Path Allocated to
double *** communication_density;

int **numRepeaters;

int layer0total = 0;
int layer1total = 0;
int layer2total = 0;
int layer3total = 0;

int ***pathsDone;
ofstream cantAdd("Unable_add.txt");
int **pathsInLayer;
int **pathsInLayer2;
int *currInLayer;
int *currInLayer2;
int total_number_paths = 0;

ofstream dvfsOutput("dvfs_output.txt");
ofstream currentDecision("current_decision.txt");
ofstream sourceDestination("sourceDestination.txt");
ofstream openVirts("openVirts.txt");
ofstream linkUsage("linkUsage.txt");
ofstream flitInjected("linkInjected.txt");
ofstream wireless("linkWireless.txt");
ofstream pairwiseLatency("pairwise_latency.txt");

double vfiClustering[4];
ifstream vfiInput;
ifstream cluster;
int clusterMatrix[NUM_IPS];
int ** linkNums;

//min span tree things:
int max_hop_count;
int min_hop_count;
int avglength;
int maxmaxlength;
int minlength;
int maxlength;
int** lookup;
int** connection;
int** lookupcycle;
int* path;
int* superpath;
int connection_type;

int traffic_optim;
int optim;
int failure;
int hop;
int** orighop;
int** ohop;
int** nhop;
int numWireless;
int numFail;
int** orig_c;
int** old_c;
int** new_c;

double avgBW = 0;
int BWhelper = 0;
int BWhelper2 = 0;


int ips_per_bus;
int *tempAddr;
int varyParam;		// the parameter that is to be varied
int runs;			// determines how many times a simulation is run
int step;			// increment for stat updates on display
int top_type = 0;	// topology type
int injection_type = 0;
float a_on = 1.9;
float a_off = 1.9;
int inject_port;	// the switch port IPs will inject into.
int octoDim = 1;	// for multidimesnional octagon only
int cycles = 0;		// simulation time in cycles 
int maxLatency = 4000;	// for histogram calculation
int maxMessage = 1200;
int DUR =  1000000;		// duration of simulation in cycles
int reset = 10000;		// time when stats are reset for transient effects
int numBuses = 0;	// Number of buses (cluster)
int numNodes = 24;	// number of nodes
int numSwitches = 28;	// number of switches in the network
int numPorts = 8;	// 6 ports, 0=c0 1=c1 2=c2 3=c3 4=p0 5=p1
int numVirts = 1;	// number of virtual channels used
int bufferDepth = 1;	// number of flits each buffer can hold
int numIps = 16;	// number of ips in tree network
int numIpsUsed = 16;// number of ips that communicate

int traffic = 0;    // type off traffic 0=uniform 1=complement 2=hotspot 3=localized
int numHotspots;	// number of hotspots
int *hotspots;		// stores node addresses of hotspots
int *con_hotspots;
int hotPercent;		// percent of messages that are sent to hotspots

int numTranspose;
int **transpose;
int **con_transpose;
int transPercent;
int ttt = 1;

int **FFTmatrix;

int msgl = 16;		// length of messages in flits
int msgIndex = 1;	// current index of messages being created
int activeMessages;	// running total of the number of active messages. 
int levels = 3;		// number of levels including ips
int messages_done = 0;	// total number of messages completed.
int messages_done0 = 0;	// total number of messages completed.
int messages_done1 = 0;	// total number of messages completed.
int messages_done2 = 0;	// total number of messages completed.
int messages_done3 = 0;	// total number of messages completed.
int network_latency = 0;
int total_latency = 0;	// running total of latency used in avg. lat calcultation
int total_latency0 = 0;	// running total of latency used in avg. lat calcultation
int total_latency1 = 0;	// running total of latency used in avg. lat calcultation
int total_latency2 = 0;	// running total of latency used in avg. lat calcultation
int total_latency3 = 0;	// running total of latency used in avg. lat calcultation
int internode_moves=0; // number of internode moves this turn
int intranode_moves=0; // number of intranode moves this turn
long internode_total=0;	// total number of link traversals
long internode_z=0;     // for 3D CUBE
long internode_local=0;	// for octom256 & trees
long internode_mid=0;	// for octom256 & trees
long internode_long=0;	// for octom256 & trees
long temp_internode_local=0;	// for octom256 & trees
long temp_internode_mid=0;	// for octom256 & trees
long temp_internode_long=0;	// for octom256 & trees

long intranode_header_total=0; // total number of header switch traversals
long intranode_data_total=0; // total number of data flit switch traversals
long temp_internode_total=0;	// total number of link traversals
long temp_intranode_header_total=0; // total number of header switch traversals
long temp_intranode_data_total=0; // total number of data flit switch traversals
double total_energy=0;
int token=0;			// determines which virtual channel goes first
int port_token=0;		// determines which port is first when routing
int counter=0;			
int temp_done = 0;	
int temp_lat = 0;
float *vary;						// holds parameter values during sweeps
int *to_internode_move_ports;	// ports marked for o_buff -> i_buff travel (destination port)
int *to_internode_move_oldports;// ports marked for o_buff -> i_buff travel (source port)
int *to_intranode_move_ports;	// ports marked for i_buff -> o_buff travel	(dest port)
int *to_intranode_move_oldports;	// ports marked for i_buff -> o_buff travel (source port)
int *to_internode_move_flits; // flits marked for o_buff -> i_buff travel
int *to_intranode_move_flits; // flits marked for i_buff -> o_buff travel
int *to_internode_move_virts; // virtual channels marked for o_buff -> i_buff travel
int *to_intranode_move_virts; // virtual channels marked for i_buff -> o_buff travel
int *to_internode_move_oldvirts; // virtual channels marked for o_buff -> i_buff travel (source)
int *to_intranode_move_oldvirts; // virtual channels marked for i_buff -> o_buff travel (source)
int *latency_histogram;			// stores histogram data
int *arrival_histogram;			
int *free_lanes;
int *cube_dimensions;			// stores dimensions of cube
int total_num_of_ports;
int queueSize;
int temp_avg_queue_size;
int avg_queue_size;
int octoTraffic;			// determines if octo traffic is cycle limited
int RES_TOKEN1;
int RES_TOKEN2;
int GHOST;
int select_function;		// determine how collisions are handled.  0 - port order 1 - oldest, 2 - round robin, 3 - priorirty

int *bus;
int local_bus_tot;
int far_bus_tot;
int numActiveMsgs;			// holds number of active msgs
int firstMsg;				// start of linked list
msg *firstCollision;		// start of linked list
int currentMsg;				// index of end of line
header *headers;				// to find collisions

// new MESH, TORUS variables
int dimensions;				// number of dimensions
int maxDim;					// the largest radix of all dimensions i.e. max(dim0,dim1,dim2...)
int xnodes;					// number of nodes in x dimension
int ynodes;					// number of nodes in y dimension
int ip_per_switch;			// number of IPs per switch
int num_layers;				// number of layers in stacked MESH
int num_buses;				// number of buses in a stacked or clustered MESH network
bool cluster_bus_network = false; // If cluster bus network

float load;					// 0-1, rate of input
float local;
float mid;
float long_distance;
bool DUMP;						// for debugging
bool TEST;						// for debugging
bool PRINTADJ;					// for debugging
bool PORTSDUMP;					// for debugging
bool GATEDUMP;
bool AVGQ;
bool ACTMSGS;
bool SAT;
bool WRAP;						// if wraparound links are used for k-ary n-cubes
bool RUNONCE;
bool USETRACE;


// for trace file 
int tr_time, tr_src;		// store the last time and source pair for a new message
int tr_counter, numTraces;	// the running counter for messages taken from the file, and the total number of traces.  Listed first in the file
bool tr_input;				// indicates if the process trace injection function needs to input from file again
int tr_msgs;

port *ports;		// holds buffer information for each port
ip *ips;		// holds info about ips like generate
msg  *msgs;			// holds infor about messages
ofstream outFile("dump.txt");
ofstream resultFile("outputFile.txt");
ofstream messagesFile("messages.txt");
ofstream linkuseFile("linkuse.txt");
ofstream latencyHistogramFile("latHist.txt");
ofstream adjacentcyListFile("adjlist.txt");
ofstream portsFile("ports.txt");
ofstream gateFile("gateways.txt");
ofstream loadFile("load.txt");
ofstream octoOut("octo.txt");
ofstream arrivalHistogramFile("arrHist.txt");
ofstream messageDump("messageDumpFile.txt");
ifstream traceFile;
ifstream superSPortMap;

// Get rid of these soon!!
double total_router_energy = 10.899;
double routing_energy = 0.3035;
double other_router_energy = total_router_energy - routing_energy;
double interconnect_energy = 0.55*32;
double interconnect_special = 0.044*32;
double interconnect_bus = 0.0974*32;
double bus_total = 5.4;




// FUNCTION DECLARATIONS ***************************
void update_network();
void set_internode_moves(int a, int b, int c, int d);
void process_intranode_moves();
void process_internode_moves();
void process_injections();
void process_trace_injections();
void inject_from_trace(int src);
void process_consumptions();
void set_intranode_moves(int a, int b, int c, int d);
void initialize_network(char * topology0);
void reinitialize_network();
void detect_collisions();
void detect_blocking();
void generate_source_and_dest(int i, int a);
int route_from_child(int node, int m, int l);
int find_oldest(int node,int a, int b);
int calc_active_msgs();
int find_level_bft(int nd);
int find_level_kary(int nd);
float find_largest_param();
void dump();
void print5();
void print12();		
void print22();	
void print24();
void printRing();
void printRingHeader();
void dump_adjacentcy();
void dump_ports();
void dump_gateways();
void connect_kary_tree(int startnode,int num);
int int_rand(int);
float float_rand(float);
int get_cube_dist_mesh(int* c1, int* c2);
int get_clustred_dist_mesh(int* c1, int* c2);
int get_stacked_dist_mesh(int* c1, int* c2);
int get_cube_dist_torus(int* c1, int* c2);
int get_cube_address(int *coords);
int get_clustered_address(int *coords);
int get_stacked_address(int *coords);
int get_bft_address(int *coords);
void get_cube_rel_addr(int address);  // this stores rel_addr at pointer tempAddr
void get_clustered_rel_addr(int address);  // this stores rel_addr at pointer tempAddr
void get_stacked_rel_addr(int address);  // this stores rel_addr at pointer tempAddr
void get_bft_rel_addr(int address);   // this stores rel_addr at pointer tempAddr
float get_exp_dist(float mean);
int tree_route(int m);
int route_octom(int m);
int route_octom256(int m);
int mypow(int x, int pow);
void initbenchmark__flags(void);
//int ring_route(int m); 
//int mesh_route(int m);

int cube_route_mesh(int m);
int cube_route_torus(int m);
int clustered_route_mesh(int m);
int clustered_route_torus(int m);
int stacked_route_mesh(int m);
int stacked_route_torus(int m);
void add_msg_to_list(int i);
void remove_msg_from_list(int i);
void print_active_msgs();
void printBus();
void update_bus_network();
void set_bus_moves();
int max(int x, int y);

//super switch and min span tree
int ss_route_mesh(int m);
int ss_route_bft(int m);
int ss_route_rand(int m);
void minspantree(int length, int hop_count, int start, int current, int dest, int pathLength, bool wireless);
void make_connect_rand(int N, int S, int ks, int kmax, double alpha);
//optim
void addWireless();

//START of mst stuff
void mst_prim(int tree_number);
double maxLength(void);
void BFS(int tree_number);
int ss_route_mst(int current_switch, int destination_switch, int tree_number);
void Dijkstra(int source);
void addWirelessToSW(void);
void checkTokens(void);
void initWirelessTokens(void);
void makeFij(void);

void buildRoutingTables(void);
void freeRoutingTables(void);
void updateWirelessLinks(int t1, int t2, int t3);
void request_analyses(void);
void updateRoutingTables(int router);
int thermalRerout(int currentRouter, int destinationRouter, int previousRouter, int tree_number);
int tupleDifference(int *address1, int *address2);
bool badPath(int currentRouter, int destinationRouter, int nextRouter, int tree_number); //return true if it is BAD path
//END of mst stuff

void removeFromLayer(int layer, int rcount, int ccount, int pathNumber);
bool addToLayer(int layer, int rcount, int ccount, int pathNumber);
bool checkDependency(int layer, int first, int second, int third, int initial, int next, int count);
int determine_path(int msgNum);

void layering_lash();
void layering_alash();
void initialize_benchmarks();

// FUNCTIONS ***************************************

void initialize_network(char * topology0){
	int helpmeout = 0;
	token1 = channel_1_node[0];
	token2 = channel_2_node[0];
	token3 = channel_3_node[0];
	if (top_type==CUBE || top_type==SUPERS) 
		tempAddr = (int*) calloc (dimensions, sizeof(int));
	if (top_type==CLUSTERED) 
		tempAddr = (int*) calloc (dimensions+1, sizeof(int));
	if (top_type==STACKED) 
		tempAddr = (int*) calloc (dimensions+1, sizeof(int));
	if (top_type==BFT || top_type==KARY) 
		tempAddr = (int*) calloc (levels, sizeof(int));

	maxMessage=2*numNodes*numVirts*(6/5);
	cout << "maxMessage= " << maxMessage << endl;

	for(int i = 0; i < NUM_IPS; i++)
	{
		for(int j = 0; j < NUM_IPS; j++)
		{
			flitsPerLink[i][j] = 0;
		}
	}
	if (top_type==OCTO5) 
		total_num_of_ports=300;
	else if(top_type == STACKED) 
		total_num_of_ports = numNodes*numPorts + num_buses*num_layers;
	else 
		total_num_of_ports = numNodes*numPorts;

	if (top_type==HBUS){
		total_num_of_ports=64;
		bus = (int*) calloc  (16,sizeof(int));
	}

	local_bus_tot = 0;
	far_bus_tot = 0;
	numActiveMsgs = 0;
	firstMsg=-1;
	currentMsg=-1;
	headers = (header*) calloc (total_num_of_ports, sizeof(header));

	if (top_type==BFT) 
		free_lanes = (int*) calloc (2, sizeof(int));		// stores number of free lanes in given parent port
	if (top_type==KARY) 
		free_lanes = (int*) calloc (numPorts/2, sizeof(int));		// stores number of free lanes in given parent port

	ports = (port*) calloc (total_num_of_ports, sizeof(port));
	ips = (ip*) calloc (numIps, sizeof(ip));
	to_internode_move_ports = (int*) calloc (total_num_of_ports, sizeof(int));
	to_internode_move_oldports = (int*) calloc (total_num_of_ports, sizeof(int));
	to_internode_move_flits = (int*) calloc (total_num_of_ports, sizeof(int));
	to_internode_move_virts = (int*) calloc (total_num_of_ports, sizeof(int));
	to_internode_move_oldvirts = (int*) calloc (total_num_of_ports, sizeof(int));
	to_intranode_move_ports = (int*) calloc (total_num_of_ports, sizeof(int));
	to_intranode_move_oldports = (int*) calloc (total_num_of_ports, sizeof(int));
	to_intranode_move_flits = (int*) calloc (total_num_of_ports, sizeof(int));
	to_intranode_move_virts = (int*) calloc (total_num_of_ports, sizeof(int));
	to_intranode_move_oldvirts = (int*) calloc (total_num_of_ports, sizeof(int));

	msgs = (msg*) calloc (maxMessage, sizeof(msg));

	// Allocate Space for messages
	for (int b=0 ; b < maxMessage; b++){
		msgs[b].header_moved=false;
		msgs[b].header_done=false;
		msgs[b].next=-1;
		msgs[b].header_in=false;
		msgs[b].wait = -1;
		if (top_type==BFT||top_type==KARY){
			msgs[b].dest = (int*) calloc (levels, sizeof(int));
			msgs[b].source = (int*) calloc (levels, sizeof(int));
			msgs[b].path = (int*) calloc (((levels+1)*4) +1, sizeof(int));
			msgs[b].vpath = (int*) calloc (((levels+1)*4) +1, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==CUBE){
			msgs[b].dest = (int*) calloc (dimensions, sizeof(int));
			msgs[b].source = (int*) calloc (dimensions, sizeof(int));
			msgs[b].path = (int*) calloc (((numIps)*4) +1, sizeof(int));
			msgs[b].vpath = (int*) calloc (((numIps)*4) +1, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type == SUPERS)
		{
			msgs[b].dest = (int*) calloc (dimensions, sizeof(int));
			msgs[b].source = (int*) calloc (dimensions, sizeof(int));
			msgs[b].path = (int*) calloc (((numIps)*numPorts) +1, sizeof(int));
			msgs[b].vpath = (int*) calloc (((numIps)*numPorts) +1, sizeof(int));
			msgs[b].path_history = (int *) calloc((numIps)*4+1, sizeof(int));
			msgs[b].end_time=-1;
		}

		if (top_type==RING || top_type==HBUS){
			msgs[b].dest = (int*) calloc (1, sizeof(int));
			msgs[b].source = (int*) calloc (1, sizeof(int));
			msgs[b].path = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].vpath = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==MESH || top_type==TORUS){
			msgs[b].dest = (int*) calloc (1, sizeof(int));
			msgs[b].source = (int*) calloc (1, sizeof(int));
			msgs[b].path = (int*) calloc (numIps*3, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==OCTO){
			msgs[b].dest = (int*) calloc (1, sizeof(int));
			msgs[b].source = (int*) calloc (1, sizeof(int));
			msgs[b].path = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].vpath = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==OCTO5){
			msgs[b].dest = (int*) calloc (2, sizeof(int));
			msgs[b].source = (int*) calloc (2, sizeof(int));
			msgs[b].path = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].vpath = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==OCTOM || top_type==OCTOM3 || top_type==OCTOM256){
			msgs[b].dest = (int*) calloc (octoDim, sizeof(int));
			msgs[b].source = (int*) calloc (octoDim, sizeof(int));
			msgs[b].path = (int*) calloc (octoDim*8, sizeof(int));
			msgs[b].vpath = (int*) calloc (numIps*2, sizeof(int));
			msgs[b].end_time=-1;
		}		
		if (top_type==CLUSTERED){
			msgs[b].dest = (int*) calloc (dimensions+1, sizeof(int));
			msgs[b].source = (int*) calloc (dimensions+1, sizeof(int));
			msgs[b].path = (int*) calloc (((numSwitches)*4) +1, sizeof(int));
			msgs[b].vpath = (int*) calloc (((numSwitches)*4) +1, sizeof(int));
			msgs[b].end_time=-1;
		}
		if (top_type==STACKED){
			msgs[b].dest = (int*) calloc (dimensions+1, sizeof(int));
			msgs[b].source = (int*) calloc (dimensions+1, sizeof(int));
			msgs[b].path = (int*) calloc (((numSwitches+num_buses)*4) +1, sizeof(int));
			msgs[b].vpath = (int*) calloc (((numSwitches+num_buses)*4) +1, sizeof(int));
			msgs[b].end_time=-1;
		}
	}
	// Allocate Space for virtual channel buffers
	for (int c = 0; c < total_num_of_ports; c++)
	{
		ports[c].i_buff = (int*) calloc (numVirts*bufferDepth, sizeof(int));
		ports[c].o_buff = (int*) calloc (numVirts*bufferDepth, sizeof(int));
		to_internode_move_ports[c]=0;
		to_internode_move_oldports[c]=0;
		to_internode_move_flits[c]=0;
		to_internode_move_virts[c]=-1;
		to_internode_move_oldvirts[c]=-1;
		to_intranode_move_ports[c]=0;
		to_intranode_move_flits[c]=0;
		to_intranode_move_virts[c]=-1;
		to_intranode_move_oldvirts[c]=-1;

		for (int r = 0; r < numVirts*bufferDepth; r++)
		{
			ports[c].i_buff[r]=0;
			ports[c].o_buff[r]=0;
		}
	}

	// Allocate Space for IPs
	for (int m=0; m < numIps; m++)
	{
		ips[m].consume_msgs = (int*) calloc (numVirts, sizeof(int));
		ips[m].consume = (int*) calloc (numVirts, sizeof(int));
		ips[m].generate = (int*) calloc (numVirts, sizeof(int));
		ips[m].generate_msgs = (int*) calloc (numVirts, sizeof(int));
		ips[m].queue = (int*) calloc (queueSize, sizeof(int));
		ips[m].queue_dest = (int *) calloc (queueSize, sizeof(int));

		for (int y=0; y < numVirts; y++)
		{
			ips[m].consume_msgs[y]=0;
			ips[m].consume[y]=0;
			ips[m].generate[y]=0;
			ips[m].generate_msgs[y]=0;
		}

		for (int y=0; y < queueSize; y++)
		{
			ips[m].queue[y]=-1;
			ips[m].queue_dest[y] = -1;
		}
	}

	latency_histogram = (int*) calloc (maxLatency+1, sizeof(int));
	arrival_histogram = (int*) calloc (DUR/100, sizeof(int));

	for (int m=0; m < maxLatency+1; m++)
		latency_histogram[m]=0;

	for (int m=0; m < DUR/100; m++)
		arrival_histogram[m]=0;



	// Actually connect network
	if (top_type==KARY)
	{
		int k=numPorts/2;
		for (int a = 0; a < numIps; a++)
		{	// level 0-1, 1-0 links
			ports[a*numPorts + k].next = (numIps+ ((int)a/k))*numPorts  + a%k;		
			ports[(numIps+ ((int)a/k))*numPorts  + a%k].next = a*numPorts + k;
		}	

		if (levels>1) connect_kary_tree(numNodes-numSwitches/levels,numSwitches/levels);
	}

	if (top_type==BFT)
	{

		int offset = 0;
		int i = 0;
		int lp=0;
		int lm=0;
		int ln=0;

		for (int a = 0; a < numIps; a++)
		{	// level 0-1, 1-0 links
			ports[a*numPorts + 4].next = (numIps+ ((int)a/4))*numPorts  + a%4;		
			ports[(numIps+ ((int)a/4))*numPorts  + a%4].next = a*numPorts + 4;
		}	
		for (int l = 1; l < levels; l++)
		{
			for (int a = 0; a < numIps/(int)pow((float)2,(l+1)); a++)
			{			
				offset=0;
				for (int x=1; x < l; x++)
					offset=offset+numIps/(int)pow((float)2,(x+1));

				lp=(int)pow((float)2,(l+1));
				lm=(int)pow((float)2,(l-1));
				ln=(int)pow((float)2,(l));
				i = (int)((a%lp)/lm);
				ports[(numIps + a + offset)*numPorts+4].next = numPorts*(offset + numIps+numIps/lp + (int)(a/lp)*ln + a%ln) + i;
				ports[(numIps + a + offset)*numPorts+5].next = numPorts*(offset + numIps+numIps/lp + (int)(a/lp)*ln + (a+lm)%ln) + i;
				ports[numPorts*(offset + numIps+numIps/lp + (int)(a/lp)*ln + a%ln) + i].next = (numIps + a + offset)*numPorts+4;
				ports[numPorts*(offset + numIps+numIps/lp + (int)(a/lp)*ln + (a+lm)%ln) + i].next = (numIps + a + offset)*numPorts+5;
				if (PRINTADJ) adjacentcyListFile << numIps + a + offset << ",4 - " << offset+numIps+numIps/lp + (int)(a/lp)*ln + a%ln << "," << i << endl; 
				if (PRINTADJ) adjacentcyListFile << numIps + a + offset << ",5 - " << offset+numIps+numIps/lp + (int)(a/lp)*ln + (a+lm)%ln << "," << i << endl; 
			}	
		}
	}

	if (top_type == SUPERS)
	{
		if (connection_type == 5)
		{
			int rcount = 0;
			int ccount = 0;
			int pcount = 0;
			int tnode = 0;


			cout << endl;
			minlength = 12;
			maxlength = 12;
			min_hop_count = 2560;
			max_hop_count = 2560;
			lookup = (int**) calloc(numNodes, sizeof(int*));
			for(rcount = 0; rcount < numNodes; rcount++)
			{
				lookup[rcount] = (int*) calloc(numNodes, sizeof(int));
			}
			path = (int*) calloc(numNodes, sizeof(int));
			superpath = (int*) calloc(numNodes, sizeof(int));

			for(rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					lookup[rcount][ccount] = -1;
				}
				path[rcount] = -1;
				superpath[rcount] = -1;
			}

			//START OF USING PREVIOUS CONNECTION ESTABLISHED EARLIER
			//connection needs to be built before this spot, other functions/code require it to be finished here
			ifstream sw_connection_s(topology0); // yuchen: topology specification
			int temp_connection = 0;
			int noOFconnection=0;
			if(!sw_connection_s.good())
			{
				cout << endl << "Error in opening 'sw_connection.txt'" << endl;
				cout << "Please make sure that the above file exists!" << endl << endl;
			}
			else
			{
				for(rcount = 0; rcount < numNodes; rcount++)
				{
					for(ccount = 0; ccount < numNodes; ccount++)
					{
						sw_connection_s >> temp_connection;
						connection[rcount][ccount] = temp_connection;
						if (rcount>63 && ccount>63 && connection[rcount][ccount]>0)
							noOFconnection++;
					}
				}
			}
			//END OF USING PREVIOUS CONNECTION FILE
			cout << "total link no:  "<< noOFconnection <<endl;
			int port_countTemp=0;
			for(int rcount = 64; rcount < numNodes; rcount++)
			  {
			    port_countTemp=0;
			    for(int ccount = 64; ccount < numNodes; ccount++)
			      {
				if ( connection[rcount][ccount]>0)
				  port_countTemp++;
			      }

			    if (port_countTemp==0)
			      cout<<"___________________Here is problem : port no:______ "<< rcount<<endl;
			  }
			if(fALASH || fLASH || fMPLASH)
			{
				for(int i=0; i<numNodes; i++)
				{
					for(int j = 0; j < numNodes; j++)
					{
						if(connection[i][j] != -1)
						{
							connections[i][j][0] = 'D';
						}
						else
							connections[i][j][0] = '.';
					}
				}
			}

			//Create lookup cycle
			int x1;
			int x2;
			int y1;
			int y2;
			int longwires = 0;
			double maxLength = 0;
			double length;
			int pathLength = 0;
			for (rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					if(connection[rcount][ccount] > 0 && rcount != ccount)
					{
						x1 = (rcount % numIps) / ((int)sqrt(numIps));
						y1 = (rcount % numIps) % ((int)sqrt(numIps));
						x2 = (ccount % numIps) / ((int)sqrt(numIps));
						y2 = (ccount % numIps) % ((int)sqrt(numIps));
						if(x1 == x2 && y1 == y2)
						{
							lookupcycle[rcount][ccount] = 1;
						}
						else
						{

							length = sqrt((double)(x2 - x1)*(x2 - x1) + (y2 - y1)*(y2 - y1));
							if(length > 10)
								longwires++;
							if(length > maxLength)
								maxLength = length;
							length = length * 20 / (2.5 * (int) sqrt(numIps));
							lookupcycle[rcount][ccount] = (int) ceil(length);
						}
					}
				}
			}
			//End Create Lookupcycle

			if(fALASH || fMPLASH || fLASH)
			{
				if(fLASH)
				{
					if(fPHYSICALDIST)
						maxPaths = 5;
					else if(!fWIRELESS)
						maxPaths = 1;
					else
						maxPaths = 2;
				}
				if(fALASH)
				{
					if(!fWIRELESS)
						maxPaths = 2;
					else
						maxPaths = 2;
				}
				int i = 0;
				int j = 0;
				int k = 0;
				int l = 0;
				flits_between_switches = (int**) calloc(numNodes, sizeof(int*)); //sourav
				MultiPathMsg = (int ****) calloc(numIps, sizeof(int ***));
				MultiPathLength = (int ***) calloc(numIps, sizeof(int **));
				MultiPathTotal = (int **) calloc(numIps, sizeof(int *));
				dependencyLayer = (int ****) calloc(numLayers, sizeof(int ***));
				dependencyCannot = (int ****) calloc(numLayers, sizeof(int ***));
				nodeUsage = (double **) calloc(numLayers, sizeof(double *));
				pathLayer = (int ***) calloc(numIps, sizeof(int **));
				communicationTotal = 0;
				communicationPerLink = (int ***) calloc(numNodes, sizeof(int **));
				for(i = 0; i < numNodes; i++)
				{
					flits_between_switches[i] = (int*) calloc(numNodes, sizeof(int)); //sourav
					communicationPerLink[i] = (int **) calloc(numNodes, sizeof(int*));
					for(j = 0; j < numNodes; j++)
					{
						communicationPerLink[i][j] = (int *) calloc(numNodes, sizeof(int));
						for( k = 0; k < numLayers; k++)
						{
							communicationPerLink[i][j][k] = 0;
						}
					}
				}
				for(i = 0; i < numIps; i++)
				{
					MultiPathMsg[i] = (int ***) calloc(numIps, sizeof(int **));
					MultiPathLength[i] = (int **) calloc(numIps, sizeof(int *));
					MultiPathTotal[i] = (int *) calloc(numIps, sizeof(int));
					pathLayer[i] = (int **) calloc(numIps, sizeof(int *));
					for(j=0; j < numIps; j++)
					{
						MultiPathMsg[i][j] = (int **) calloc(maxPaths, sizeof(int *));
						MultiPathLength[i][j] = (int *) calloc(maxPaths, sizeof(int));
						MultiPathTotal[i][j] = 0;
						pathLayer[i][j] = (int *) calloc(maxPaths, sizeof(int));
						for(k = 0; k < maxPaths; k++)
						{
							pathLayer[i][j][k] = -1;
							MultiPathMsg[i][j][k] = (int *) calloc(maxPathLength, sizeof(int));
							MultiPathLength[i][j][k] = 0;
							for(l = 0; l < maxPathLength; l++)
							{
								MultiPathMsg[i][j][k][l] = -1;
							}
						}
					}
				}
				for(i = 0; i < numLayers; i++)
				{
					nodeUsage[i] = (double *) calloc(numIps+numSwitches, sizeof(double));
					dependencyLayer[i] = (int ***) calloc(numIps+numSwitches, sizeof(int **));
					dependencyCannot[i] = (int ***) calloc(numIps+numSwitches, sizeof(int **));
					for(j = 0; j < (numIps+numSwitches); j++)
					{
						nodeUsage[i][j] = 0.0;
						dependencyLayer[i][j] = (int **) calloc(numIps+numSwitches, sizeof(int *));
						dependencyCannot[i][j] = (int **) calloc(numIps+numSwitches, sizeof(int *));
						for(k = 0; k < (numIps+numSwitches); k++)
						{
							dependencyLayer[i][j][k] = (int *) calloc(numIps+numSwitches, sizeof (int ));
							dependencyCannot[i][j][k] = (int *) calloc(numIps+numSwitches, sizeof(int));
							for(l = 0; l < numIps+numSwitches; l++)
							{
								dependencyLayer[i][j][k][l] = 0;
								dependencyCannot[i][j][k][l] = 0;
							}
						}
					}
				}
			}
			if(fSTART)
			{
				avglength = 0;
				for(rcount = 0; rcount < numIps; rcount++)
				{
					cout << ".";
					for(ccount = 0; ccount < numIps; ccount++)
					{
						pathLengthRepeaters[rcount][ccount][0] = 0;
						pathLengthRepeaters[rcount][ccount][1] = 0;
						helpmeout = 0;
						if (rcount != ccount)
						{
							//reset values
							min_hop_count = max_hop_count;
							minlength = maxlength;
							minPath = 1000000;
							for(pcount = 0; pcount < numNodes; pcount++)
							{
								path[pcount] = -1;
								superpath[pcount] = -1;
							}
							minspantree(0, 0, rcount, rcount, ccount, 0, false);
							//do stuff with superpath and lookup, they should be current!
							if (superpath[minlength] != ccount)
							{
								helpmeout = 1;
								cout << rcount << "," << ccount << endl;
								if ((ccount < numIps) && (rcount < numIps))
								{
									cout << "\n\\\\\\\\\\\\\\\\\\\\ERROR HAS HAPPENED FOR SOURCE\\DEST PAIR (" << rcount << "\\" << ccount << ")!" << endl;
								}
							}
							lookup[rcount][ccount] = superpath[1];
							//if((fLASH || fMPLASH ) && !fPHYSICALDIST)
							//{
								if(rcount < numIps && ccount < numIps)
								{
									MultiPathLength[rcount][ccount][0] = minlength+1;
									for(int i = 0; i < MultiPathLength[rcount][ccount][0]; i++)
									{
										MultiPathMsg[rcount][ccount][0][i] = superpath[i];
									}
								}
								pathLengthRepeaters[rcount][ccount][0] = minPath;
							//}
							avglength += minlength;
							if (minlength > maxmaxlength)
							{
								maxmaxlength = minlength;
							}
						}
					}
				}
			}

			int totalPaths = 0;
			for(rcount = 0; rcount < numIps; rcount++)
			{
				for(ccount = 0; ccount < numIps; ccount++)
				{
					if(rcount != ccount)
					{
						for(int i = 1; i < maxPaths; i++)
						{
							if(MultiPathLength[rcount][ccount][0] < MultiPathLength[rcount][ccount][i])
								MultiPathLength[rcount][ccount][i] = -1;
							else
								totalPaths++;
						}
					}
				}
			}

			

			if((fLASH || fMPLASH || fALASH) && fSTART)
			{
				pathsDone = (int ***) calloc(numIps, sizeof(int **));
				pathsInLayer = (int **) calloc(numLayers, sizeof(int *));
				currInLayer = (int *) calloc(numLayers, sizeof(int));
				pathsInLayer2 = (int **) calloc(numLayers, sizeof(int *));
				currInLayer2 = (int *) calloc(numLayers, sizeof(int));

				numPerLayer = (int *) calloc(numLayers, sizeof(int));
				for(int i = 0; i < numIps; i++)
				{
					pathsDone[i] = (int **) calloc(numIps, sizeof(int *));
					for(int j = 0; j < numIps; j++)
					{
						pathsDone[i][j] = (int *) calloc(maxPaths, sizeof(int));
						for(int k = 0; k < maxPaths; k++)
						{
							pathsDone[i][j][k] = 0;
						}
					}
				}
				for(int i = 0; i < numLayers; i++)
				{
					currInLayer[i] = 0;
					numPerLayer[i] = 0;
					currInLayer2[i] = 0;
					pathsInLayer[i] = (int *) calloc(numIps*(numIps-1)*maxPaths, sizeof(int));
					pathsInLayer2[i] = (int *) calloc(numIps*(numIps-1)*maxPaths, sizeof(int));
					for(int j = 0; j < numIps*(numIps-1)*maxPaths; j++)
					{
						pathsInLayer[i][j] = -1;
						pathsInLayer2[i][j] = -1;
					}
				}
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						for(int k = 0; k < maxPaths; k++)
						{
							if(MultiPathLength[i][j][k] > 0)
								total_number_paths++;
						}
					}
				}
			}
			if(fWIRELESS)
			{
				for(int i = 0; i < channel_1_nodes; i++)
				{
					for(int j = i; j < channel_1_nodes; j++)
					{
						if(i != j)
						{
							connections[channel_1_node[i]][channel_1_node[j]][0] = '1';
							connections[channel_1_node[j]][channel_1_node[i]][0] = '1';
							connection[channel_1_node[i]][channel_1_node[j]] = 10;
							connection[channel_1_node[j]][channel_1_node[i]] = 10;
							lookupcycle[channel_1_node[i]][channel_1_node[j]] = 1;
							lookupcycle[channel_1_node[j]][channel_1_node[i]] = 1;
						}
					}
				}
				for(int i = 0; i < channel_2_nodes; i++)
				{
					for(int j = i; j < channel_2_nodes; j++)
					{
						if(i != j)
						{
							connections[channel_2_node[i]][channel_2_node[j]][0] = '2';
							connections[channel_2_node[j]][channel_2_node[i]][0] = '2';
							connection[channel_2_node[i]][channel_2_node[j]] = 10;
							connection[channel_2_node[j]][channel_2_node[i]] = 10;
							lookupcycle[channel_2_node[i]][channel_2_node[j]] = 1;
							lookupcycle[channel_2_node[j]][channel_2_node[i]] = 1;
						}
					}
				}
				for(int i = 0; i < channel_3_nodes; i++)
				{
					for(int j = i; j < channel_3_nodes; j++)
					{
						if(i != j)
						{
							connections[channel_3_node[i]][channel_3_node[j]][0] = '3';
							connections[channel_3_node[j]][channel_3_node[i]][0] = '3';
							connection[channel_3_node[i]][channel_3_node[j]] = 10;
							connection[channel_3_node[j]][channel_3_node[i]] = 10;
							lookupcycle[channel_3_node[i]][channel_3_node[j]] = 1;
							lookupcycle[channel_3_node[j]][channel_3_node[i]] = 1;
						}
					}
				}
				if(fSTART)
				{
					avglength = 0;
					for(rcount = 0; rcount < numIps; rcount++)
					{
						cout << ".";
						for(ccount = 0; ccount < numIps; ccount++)
						{
							helpmeout = 0;
							pathLengthRepeatersWI[rcount][ccount] = 0;
							if (rcount != ccount)
							{
								//reset values
								minPath = 1000000;
								min_hop_count = max_hop_count;
								minlength = maxlength;
								for(pcount = 0; pcount < numNodes; pcount++)
								{
									path[pcount] = -1;
									superpath[pcount] = -1;
								}
								minspantree(0, 0, rcount, rcount, ccount, 0, true);
								//do stuff with superpath and lookup, they should be current!
								if (superpath[minlength] != ccount)
								{
									helpmeout = 1;
									if ((ccount < numIps) && (rcount < numIps))
									{
										cout << "\n\\\\\\\\\\\\\\\\\\\\ERROR HAS HAPPENED FOR SOURCE\\DEST PAIR (" << rcount << "\\" << ccount << ")!" << endl;
									}
								}
								lookup[rcount][ccount] = superpath[1];
								if(rcount < numIps && ccount < numIps)
								{
									MultiPathLength[rcount][ccount][wirelessPathNum] = minlength+1;
									for(int i = 0; i < MultiPathLength[rcount][ccount][wirelessPathNum]; i++)
									{
										MultiPathMsg[rcount][ccount][wirelessPathNum][i] = superpath[i];
									}
								}
								pathLengthRepeatersWI[rcount][ccount] = minPath;

								avglength += minlength;
								if (minlength > maxmaxlength)
								{
									maxmaxlength = minlength;
								}
							}
						}
					}
				}
			}

			if(fALASH)
			{
				for(rcount = 0; rcount < numIps; rcount++)
				{
					for(ccount = 0; ccount < numIps; ccount++)
					{
						int i = 0;
						for(i = 1; i < maxPaths; i++) //Remove Longer Wireline Paths
						{
							if(MultiPathLength[rcount][ccount][i] > MultiPathLength[rcount][ccount][0] || MultiPathLength[rcount][ccount][i] == 0)
							{
								MultiPathLength[rcount][ccount][i] = -1;
								for(int j = 0; j < maxPathLength; j++)
								{
									MultiPathMsg[rcount][ccount][i][j] = -1;
								}
							}
						}
					}
				}
			}

			if((fALASH || fLASH) && fWIRELESS)
			{
				for(rcount = 0; rcount < numIps; rcount++)
				{
					for(ccount = 0; ccount < numIps; ccount++)
					{
						int i = 0;

						bool WirelessPath = false;

						if(MultiPathLength[rcount][ccount][0] == MultiPathLength[rcount][ccount][wirelessPathNum])
						{
							MultiPathLength[rcount][ccount][wirelessPathNum] = -1;
							continue;
						}

						for(i = 0; i < MultiPathLength[rcount][ccount][wirelessPathNum]-2; i++) //Look for wireless paths
						{
							if(connections[MultiPathMsg[rcount][ccount][wirelessPathNum][i]][MultiPathMsg[rcount][ccount][wirelessPathNum][i+1]][0] != 'D')
							{
								WirelessPath = true;
								break;
							}
						}
						if(!WirelessPath) //Remove Nonwireless Paths in wireless path slot
							MultiPathLength[rcount][ccount][wirelessPathNum] = -1;
						if(MultiPathLength[rcount][ccount][wirelessPathNum] != -1)
						{
							int wi_switch = MultiPathMsg[rcount][ccount][wirelessPathNum][i] - numIps;
							if((MultiPathLength[rcount][ccount][0] + wirelessPathThreshold) < (i + MultiPathLength[wi_switch][ccount][0]-1)) //Remove paths with high penalty
								MultiPathLength[rcount][ccount][wirelessPathNum] = -1;
						}
					}
				}
				int number_wireless = 0;
				for(rcount = 0; rcount < numIps; rcount++)
				{
					for(ccount = 0; ccount < numIps; ccount++)
					{
						if(MultiPathLength[rcount][ccount][wirelessPathNum] != -1)
							number_wireless++;
					}
				}
				cout << number_wireless <<endl;
			}

			if(fWIRELESS && fLASH) //Remove the wireline paths for the sources with a wireless shortest path and not at a WI
			{
				for(rcount = 0; rcount < numIps; rcount++)
				{
					for(ccount = 0; ccount < numIps; ccount++)
					{
						bool wireless_node = false;
						if(MultiPathLength[rcount][ccount][wirelessPathNum] != -1)
						{
							for(int i = 0; i < channel_1_nodes; i++)
							{
								if(channel_1_switch[i] == rcount)
								{
									wireless_node = true;
									break;
								}
							}
							if(wireless_node == false)
							{
								for(int i = 0; i < channel_2_nodes; i++)
								{
									if(channel_2_switch[i] == rcount)
									{
										wireless_node = true;
										break;
									}
								}
							}
							if(wireless_node == false)
							{
								for(int i = 0; i < channel_3_nodes; i++)
								{
									if(channel_3_switch[i] == rcount)
									{
										wireless_node = true;
										break;
									}
								}
							}
							if(wireless_node == false)
							{
								for(int i =0 ; i < wirelessPathNum; i++)
								{
									MultiPathLength[rcount][ccount][i] = -1;
								}
								//MultiPathLength[rcount][ccount][0] = -1;
								continue;
							}
						}
					}
				}
			}
			


			

			if(fLASH && fPHYSICALDIST)
			{
				int highest = -1;
				bool **pathsChecked;
				int **pathUsed;
				pathsChecked = (bool **) calloc(numIps, sizeof(bool*));
				pathUsed = (int **) calloc(numIps, sizeof(int *));
				for(int i =0; i < (numIps+numSwitches);i++)
				{
					nodeUsage[0][i] = 0;
				}
				for(int i = 0; i < numIps; i++)
				{
					pathUsed[i] =(int *) calloc(numIps, sizeof(int));
					pathsChecked[i] = (bool *) calloc(numIps, sizeof(bool));
					for(int j =0; j < numIps; j++)
					{
						pathUsed[i][j] = -1;
					}
				}
				for(int p = 0; p < (numIps*(numIps-1)); p++)
				{
					rcount = p/numIps;
					ccount = p %numIps;
					if(MultiPathLength[rcount][ccount][wirelessPathNum] > 0)
					{
						for(int q = 0; q < MultiPathLength[rcount][ccount][wirelessPathNum]; q++)
						{
							nodeUsage[0][MultiPathMsg[rcount][ccount][wirelessPathNum][q]] += fijMatrix[rcount][ccount];
						}
					}
				}
				for(int z = 0; z < 20; z++)
				{
					for(int i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsChecked[i][j] = false;
						}
					}
					for(int p = 0; p < (numIps*(numIps-1)); p++)
					{
						highest = -1;
						for (int q = 0; q < numIps; q++)
						{
							for (int r = 0; r < numIps; r++)
							{
								if(q != r)
								{
									if((highest == -1 || fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r]) && pathsChecked[q][r] == false)
									{
										highest = q*numIps + r;
									}
								}
							}
						}
						rcount = highest/numIps;
						ccount = highest%numIps;
						pathsChecked[rcount][ccount] = true;
						
						if(MultiPathLength[rcount][ccount][0] > 0)
						{
							int bestPath = 0;
							int pathUsedPrev = -1;
							double lowest_hotspot = 100000;
							for(int q = 0; q < wirelessPathNum; q++)
							{
								if(MultiPathLength[rcount][ccount][q] > 0)
								{
									for(int r = 1; r < (MultiPathLength[rcount][ccount][q]-1); r++)
									{
										if(bestPath == pathUsed[rcount][ccount])
										{
											if(nodeUsage[0][MultiPathMsg[rcount][ccount][q][r]] < (lowest_hotspot-fijMatrix[rcount][ccount]))
											{
												bestPath = q;
												lowest_hotspot = nodeUsage[0][MultiPathMsg[rcount][ccount][q][r]];
											}
										}
										else
										{
											if(nodeUsage[0][MultiPathMsg[rcount][ccount][q][r]] < lowest_hotspot)
											{
												bestPath = q;
												lowest_hotspot = nodeUsage[0][MultiPathMsg[rcount][ccount][q][r]];
											}
										}

									}
								}
							}
							if(pathUsed[rcount][ccount] != bestPath)
							{
								if(pathUsed[rcount][ccount] != -1)
								{
									for(int q = 0; q < MultiPathLength[rcount][ccount][pathUsed[rcount][ccount]]; q++)
									{
										nodeUsage[0][MultiPathMsg[rcount][ccount][pathUsed[rcount][ccount]][q]] -= fijMatrix[rcount][ccount];
									}
								}
								for(int q = 0; q < MultiPathLength[rcount][ccount][bestPath]; q++)
								{
									nodeUsage[0][MultiPathMsg[rcount][ccount][bestPath][q]] += fijMatrix[rcount][ccount];
								}
								pathUsed[rcount][ccount] = bestPath;
							}
						}
					}
					double nodeMax = 0;
					for(int q = numIps; q < (numIps+numSwitches); q++)
					{
						if(nodeMax < nodeUsage[0][q])
							nodeMax = nodeUsage[0][q];
					}
					cout << "NodeMax: " << nodeMax << endl;
				}

				for(int q = 0; q < numIps; q++)
				{
					for(int r = 0; r < numIps; r++)
					{
						if(pathUsed[q][r] >= 0 && q != r)
						{
							for(int s = 0; s < MultiPathLength[q][r][0]; s++)
							{
								MultiPathMsg[q][r][0][s] = MultiPathMsg[q][r][pathUsed[q][r]][s];
							}
							for(int s = 1; s < wirelessPathNum; s ++)
							{
								MultiPathLength[q][r][s] = -1;
							}
						}
					}
				}
			}

			if(fLASH)
				layering_lash();
			if(fALASH)
				layering_alash();

			int linknum = 1;

			linkNums = (int **) calloc(numNodes, sizeof(int *));
			for(rcount = 0; rcount < numNodes; rcount++)
			{
				linkNums[rcount] = (int *) calloc(numNodes, sizeof(int));
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					linkNums[rcount][ccount] = 0;
				}
			}

			for(rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					if(rcount >= numIps && ccount >= numIps)
					{
						if(rcount != ccount && ccount > rcount )
						{
							if(!(rcount == (49+numIps) && ccount == (61+numIps)))

							{
								if(connection[rcount][ccount] == 1)
								{
									linkNums[rcount][ccount] = linknum++;
								}
							}
						}
						else
						{
							linkNums[rcount][ccount] = linkNums[ccount][rcount];
						}
					}
				}
			}
			linkNums[49+numIps][61+numIps] = 124;
			linkNums[61+numIps][49+numIps] = 124;



			if(fALASH && fBENCHMARK)
			{
				int total_paths = 0;
				int total_pairs = 0;
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						if(i != j) 
						{
							if(fijMatrix[i][j] > fij50)
							{
								total_pairs++;
								for(int k = 0; k < maxPaths; k++)
								{
									for(int l = 0 ; l < numLayers; l++)
									{
										if(pathAllocLayer[i][j][k][l] == 1)
											total_paths++;
									}
	 							}
							}
						}
					}
				}

				int total_unique = 0;                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       				
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						if(i != j) 
						{
							if(fijMatrix[i][j] > fij50)
							{
								for(int k = 0; k < numIps; k++)
								{
									for(int l = 0; l < numIps; l++)
									{
										if(k != l && i != k && j != l)
										{
											if(fijMatrix[k][l] > fij50)
											{
												for(int m = 0; m < maxPaths; m++)
												{
													for(int n = 0; n < numLayers; n++)
													{
														for(int o = 0; o < maxPaths; o++)
														{
															for(int p = 0; p < numLayers; p++)
															{
																if(pathAllocLayer[i][j][m][n] == 1 && pathAllocLayer[k][l][o][p] == 0 && MultiPathLength[k][l][o] > 0 && MultiPathLength[i][j][m] > 0)
																	total_unique++;
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
				cout << "total paths: " << total_paths << endl;
				cout << "Total unique: " << total_unique << endl;
				cout << "Total Pairs: " << total_pairs << endl;
			}
			int total_alloc = 0;

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int k = 0; k < maxPaths; k++)
						{
							for(int j = 0; j < numLayers; j++)
							{
							if(pathAllocLayer[i][j][k][j] == 1)
								total_alloc++;
							}
						}
					}
				}
			}

			numRepeaters = (int **) calloc(numNodes, sizeof(int *));
			for(int i = 0 ; i < numNodes; i++)
			{
				numRepeaters[i] = (int *) calloc(numNodes, sizeof(int));
				for(int j = 0; j < numNodes; j++)
				{
					numRepeaters[i][j] = 0;
				}
			}

			for(int i = 0; i < numNodes; i++)
			{
				for(int j = 0; j < numNodes; j++)
				{
					if(connection[i][j] != -1)
					{
						if(lookupcycle[i][j] > 1)
						{
							numRepeaters[i][j] = (lookupcycle[i][j]-1);
						}
					}
					else
					{
						numRepeaters[i][j] = 0;
					}
				}
			}

			int total_hops = 0;

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						if(MultiPathLength[i][j][wirelessPathNum] > 0)
							total_hops += (MultiPathLength[i][j][wirelessPathNum]-3);
						else
							total_hops += (MultiPathLength[i][j][0]-3);
					}

				}

			}
			cout << "Total number of hops: " << total_hops << endl;
			cout << "Average number of hops: " << ((double)total_hops/ (numIps*(numIps-1))) << endl;

			ofstream outputRepeaters("sw_repeaters.txt");

			for(int i = numIps; i < numNodes; i++)
			{
				for(int j = numIps; j < numNodes; j++)
				{
					if(connection[i][j] != -1)
					{
						outputRepeaters << lookupcycle[i][j] << " ";
					}
					else
					{
						outputRepeaters << "0" << " ";
					}
				}
				outputRepeaters << endl;
			}

			outputRepeaters.close();

			communication_density = (double ***) calloc(numNodes, sizeof(double **));
			for(int i = 0; i < numNodes; i++)
			{
				communication_density[i] = (double **) calloc(numNodes, sizeof(double *));
				for(int j = 0; j < numNodes; j++)
				{
					communication_density[i][j] = (double *) calloc(numLayers, sizeof( double));
					for(int k = 0; k < numLayers; k++)
					{
						communication_density[i][j][k] = 0.0;
					}
				}
			}



			/*int drawback = 0;
			int wirelessPath = 0;
			int tooLong = 0;
			for(rcount = 0; rcount < numIps; rcount++)
			{
			for(ccount = 0; ccount < numIps; ccount++)
			{
			if(rcount != ccount)
			{
			if(pathLayer[rcount][ccount][1] != -1)
			{
			int current;
			int next;
			int new_length= 0;
			wirelessPath++;
			for(int i = 0; i < MultiPathLength[rcount][ccount][1]-1; i++)
			{
			current = MultiPathMsg[rcount][ccount][1][i];
			next = MultiPathMsg[rcount][ccount][1][i+1];
			if(connections[current][next][0] != 'D')
			{
			new_length = i;
			new_length += MultiPathLength[current-numIps][ccount][0]-1;
			if(new_length > MultiPathLength[rcount][ccount][0])
			{
			drawback++;
			if(new_length >= (MultiPathLength[rcount][ccount][0]+2))
			{
			removeFromLayer(pathLayer[rcount][ccount][1],rcount, ccount, 1);
			pathLayer[rcount][ccount][1] = -1;
			tooLong++;
			}
			}
			}
			}
			}
			}
			}
			}
			*/
			for(rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
					outFile << connection[rcount][ccount] << ",";
				outFile << endl;
			}

			if(optim)
			{
				for(rcount = 0; rcount < numSwitches; rcount++)
					for(ccount = 0; ccount < numSwitches; ccount++)
						orig_c[rcount][ccount] = connection[rcount + numIps][ccount + numIps];

				addWireless();

				for(rcount = 0; rcount < numSwitches; rcount++)
				{
					free(old_c[rcount]);
					free(new_c[rcount]);
				}
				free(old_c);
				free(new_c);

				for(rcount = 0; rcount < numIps; rcount++)
				{
					free(ohop[rcount]);
					free(nhop[rcount]);
				}
				free(ohop);
				free(nhop);

				for(rcount = 0; rcount < numSwitches; rcount++)
					for(ccount = 0; ccount < numSwitches; ccount++)
						connection[rcount + numIps][ccount + numIps] = orig_c[rcount][ccount];
			}

			if (failure) //only needed if links are disconnected
			{
				int breaker = (int) (((double) (((double) numFail) / 100.0)) * ((double) numWireless));

				for(pcount = 0; pcount < breaker; pcount++)
				{
					failure = 0;

					while(!failure)
					{
						tnode = rand() % numSwitches;
						tnode += numIps;

						for(ccount = 0; ccount < numNodes; ccount++)
						{
							if ((connection[tnode][ccount] == 10) && (!failure))
							{
								failure = 1;
								connection[tnode][ccount] = -1;
								connection[ccount][tnode] = -1;
								lookupcycle[tnode][ccount] = -1;
								lookupcycle[ccount][tnode] = -1;
							}
						}
					}
				}
			}

			//now fix lookup for port addresses, not node addresses
			//node address * numPorts = port[0] of a node
			for(pcount = 0; pcount < numNodes; pcount++)
			{
				superpath[pcount] = 0;
			}

			BWhelper = 0;
			BWhelper2 = 0;
			for(rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					tnode = ccount;
					if (connection[rcount][ccount] != -1)
					{
						if (connection[rcount][ccount] == 10)
						{
							avgBW += 10;
							BWhelper2++;
						}
						else
						{
							avgBW += 2;
						}
						BWhelper++;
						connection[rcount][ccount] = (tnode * numPorts) + superpath[tnode];
						superpath[tnode]++;
					}
				}
			}
			if (fWIRELESS)
			{
				avgBW = avgBW / ((2 * (BWhelper - numWireless)) + (10 * (BWhelper2 / 2)));
			}
			else
			{
				avgBW = avgBW / (2 * BWhelper);
			}

			cout << endl;

			//for(rcount = 0; rcount < numNodes; rcount++)
			//{
			//	for(ccount = 0; ccount < numNodes; ccount++)
			//	{
			//		tnode = lookup[rcount][ccount];
			//		if (tnode != -1)
			//		{
			//			if (connection[rcount][tnode] == -1)
			//			{
			//				cout << endl << "ERROR IN CONNECTION OR LOOKUP TABLE!" << endl << endl << endl;
			//			}
			//			lookup[rcount][ccount] = connection[rcount][tnode];
			//		}
			//	}
			//}

			cout << endl;
			cout << endl << "Max length = " << maxmaxlength << endl << "Avg length = " << avglength << endl;
			outFile << endl << "Avg length = " << avglength << endl << endl << endl;

			if(fMROOTS)
			{
				for(int tree_number = 0; tree_number < MTREES; tree_number++)
				{
					BFS(tree_number);
					//mst_prim(tree_number);
				}
			}
			if(optim)
				addWirelessToSW();
			if(fMROOTS)
				buildRoutingTables();
			if(optim)
				updateWirelessLinks(token1, token2, token3);
			if(GLOBAL)
			{
				if(fMROOTS)
				{
					for(int t1 = 0; t1 < MTREES; t1++)
					{
						for(int s1 = 0; s1 < MST_N; s1++)
						{
							for(int d1 = 0; d1 < MST_N; d1++)
							{
								if(s1 != d1)
								{
									mPath[s1][d1][t1][NUM_PATHS-1].plength = 0;
									if(t1 == 3 && s1 == 51 && d1 == 10)
										t1 = t1;
									findPaths(0, s1, s1, d1, t1, None);

									//resetting of "global" variables
									ppp = 0;
									path_length = 0;
									wirelessP = 0;
								}

							}
						}
						rankPaths(t1);
					}
				}
			}

			///ROUTING WILL NOW WORK FOR LOOKUP ->>   PORT = LOOKUP[DEST][CURRENT]
			for(rcount = 0; rcount < numNodes; rcount++)
			{
				for(ccount = 0; ccount < numNodes; ccount++)
				{
					if(connection[rcount][ccount] != -1 && connection[ccount][rcount] != -1)
					{
						ports[connection[rcount][ccount]].next = connection[ccount][rcount];
						ports[connection[ccount][rcount]].next = connection[rcount][ccount];

						if(PRINTADJ)
						{
							adjacentcyListFile << connection[rcount][ccount] << " - " << connection[ccount][rcount] << endl << connection[ccount][rcount] << " - " << connection[rcount][ccount] << endl;
						}
					}
				}
			}
		}
		else
		{
			int firstNum = -1;
			int secondNum = -1;
			char comma = 'x';
			int portMapCounter = 0;

			if (!superSPortMap.is_open())
				superSPortMap.open("ssPortMap.txt",fstream::in);

			while(!superSPortMap.eof())
			{
				superSPortMap >> firstNum;
				superSPortMap >> comma;
				superSPortMap >> secondNum;
				portMapCounter++;

				if (firstNum == -1 || comma == -1 || secondNum == -1) break;
				else if (comma != ',') cout << "\n\n\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\nAn error could have occured at about line :" << portMapCounter << endl << endl;
				else
				{
					ports[firstNum].next = secondNum;
					ports[secondNum].next = firstNum;
				}

				if (PRINTADJ) adjacentcyListFile << firstNum << " - " << secondNum << endl << secondNum << " - " << firstNum << endl;
			}

			superSPortMap.close();
		}
	}

	if (top_type==CUBE)
	{
		for (int a=0;a<numIps;a++)
		{  // injection links
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;	
		}
		int *current_addr, *plusAddrRel, *minusAddrRel;
		current_addr = (int*) calloc(dimensions,sizeof(int));
		minusAddrRel = (int*) calloc(dimensions,sizeof(int));
		plusAddrRel = (int*) calloc(dimensions,sizeof(int));
		int addr=0;
		int plusAddr=0;
		int minusAddr=0;

		//for (int a=0; a < (int)(pow((float)maxDim,dimensions)); a++){
		for (int a=0; a < numSwitches; a++)
		{
			get_cube_rel_addr(a);
			for (int d=0; d<dimensions;d++)
			{
				// d is the dimension
				// keep all the digits the same, except the dimension we are building along
				for (int e=0; e<dimensions; e++)
				{
					if (e==d) {
						plusAddrRel[e]=(tempAddr[e]+1)%cube_dimensions[e];
						minusAddrRel[e]=(tempAddr[e]+cube_dimensions[e]-1)%cube_dimensions[e];
					}
					else {
						plusAddrRel[e]=tempAddr[e];
						minusAddrRel[e]=tempAddr[e];
					}
				}
				plusAddr=get_cube_address(plusAddrRel);
				minusAddr=get_cube_address(minusAddrRel);
				// minus connection on dimension d
				ports[(numIps+a)*numPorts+1+d*2].next = (numIps+minusAddr)*numPorts+2+d*2;
				ports[(numIps+minusAddr)*numPorts+2+d*2].next =(numIps+a)*numPorts+1+d*2; 
				if (PRINTADJ) adjacentcyListFile << (numIps+minusAddr)*numPorts+2+d*2 << " - " << (numIps+a)*numPorts+1+d*2 << endl;
				// plus connection on dimension d
				ports[(numIps+a)*numPorts+2+d*2].next = (numIps+plusAddr)*numPorts+1+d*2;
				ports[(numIps+plusAddr)*numPorts+1+d*2].next = (numIps+a)*numPorts+2+d*2;
				if (PRINTADJ) adjacentcyListFile << (numIps+plusAddr)*numPorts+1+d*2 << " - " << (numIps+a)*numPorts+2+d*2 << endl;
			}
		}

		free (plusAddrRel);
		free (minusAddrRel);
	}

	if (top_type==CLUSTERED){
		for (int a=0;a<numIps;a++){  // injection links
			ports[a*numPorts].next = (numIps+a/ip_per_switch)*numPorts + dimensions*2 + a%ip_per_switch;
			ports[(numIps+a/ip_per_switch)*numPorts + dimensions*2 + a%ip_per_switch].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a/ip_per_switch)*numPorts + dimensions*2 + a%ip_per_switch << " i" << endl;
		}
		int *current_addr, *plusAddrRel, *minusAddrRel;
		current_addr = (int*) calloc(dimensions,sizeof(int));
		minusAddrRel = (int*) calloc(dimensions,sizeof(int));
		plusAddrRel = (int*) calloc(dimensions,sizeof(int));
		int addr=0;
		int plusAddr=0;
		int minusAddr=0;

		//for (int a=0; a < (int)(pow((float)maxDim,dimensions)); a++){
		for (int a=0; a < numSwitches; a++){
			get_cube_rel_addr(a);
			for (int d=0; d<dimensions;d++){
				// d is the dimension
				// keep all the digits the same, except the dimension we are building along
				for (int e=0; e<dimensions; e++){
					if (e==d) {
						plusAddrRel[e]=(tempAddr[e]+1)%cube_dimensions[e];
						minusAddrRel[e]=(tempAddr[e]+cube_dimensions[e]-1)%cube_dimensions[e];
					}
					else {
						plusAddrRel[e]=tempAddr[e];
						minusAddrRel[e]=tempAddr[e];
					}
				}
				plusAddr=get_cube_address(plusAddrRel);
				minusAddr=get_cube_address(minusAddrRel);
				// minus connection on dimension d
				ports[(numIps+a)*numPorts+d*2].next = (numIps+minusAddr)*numPorts+1+d*2;
				ports[(numIps+minusAddr)*numPorts+1+d*2].next =(numIps+a)*numPorts+d*2; 
				if (PRINTADJ) adjacentcyListFile << (numIps+minusAddr)*numPorts+1+d*2 << " - " << (numIps+a)*numPorts+d*2 << endl;
				// plus connection on dimension d
				ports[(numIps+a)*numPorts+1+d*2].next = (numIps+plusAddr)*numPorts+d*2;
				ports[(numIps+plusAddr)*numPorts+d*2].next = (numIps+a)*numPorts+1+d*2;
				if (PRINTADJ) adjacentcyListFile << (numIps+plusAddr)*numPorts+d*2 << " - " << (numIps+a)*numPorts+1+d*2 << endl;
			}
		}

		free (plusAddrRel);
		free (minusAddrRel);
	}

	if (top_type==STACKED){
		for (int a=0;a<numIps;a++){  // injection links
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << " i" << endl;
		}
		int *current_addr, *plusAddrRel, *minusAddrRel;
		current_addr = (int*) calloc(dimensions,sizeof(int));
		minusAddrRel = (int*) calloc(dimensions,sizeof(int));
		plusAddrRel = (int*) calloc(dimensions,sizeof(int));
		int addr=0;
		int plusAddr=0;
		int minusAddr=0;

		for (int i=0; i < num_layers; i++) {
			for (int a=0; a < (int)(pow((float)maxDim,dimensions)); a++){
				get_cube_rel_addr(a);
				for (int d=0; d<dimensions;d++){
					// d is the dimension
					// keep all the digits the same, except the dimension we are building along
					for (int e=0; e<dimensions; e++){
						if (e==d) {
							plusAddrRel[e]=(tempAddr[e]+1)%cube_dimensions[e];
							minusAddrRel[e]=(tempAddr[e]+cube_dimensions[e]-1)%cube_dimensions[e];
						}
						else {
							plusAddrRel[e]=tempAddr[e];
							minusAddrRel[e]=tempAddr[e];
						}
					}
					plusAddr=get_cube_address(plusAddrRel);
					minusAddr=get_cube_address(minusAddrRel);
					// minus connection on dimension d
					ports[(numIps+(numIps/num_layers)*i+a)*numPorts+1+d*2].next = (numIps+(numIps/num_layers)*i+minusAddr)*numPorts+2+d*2;
					ports[(numIps+(numIps/num_layers)*i+minusAddr)*numPorts+2+d*2].next = (numIps+(numIps/num_layers)*i+a)*numPorts+1+d*2; 
					if (PRINTADJ) adjacentcyListFile << (numIps+(numIps/num_layers)*i+minusAddr)*numPorts+2+d*2 << " - " << (numIps+(numIps/num_layers)*i+a)*numPorts+1+d*2 << endl;
					// plus connection on dimension d
					ports[(numIps+(numIps/num_layers)*i+a)*numPorts+2+d*2].next = (numIps+(numIps/num_layers)*i+plusAddr)*numPorts+1+d*2;
					ports[(numIps+(numIps/num_layers)*i+plusAddr)*numPorts+1+d*2].next = (numIps+(numIps/num_layers)*i+a)*numPorts+2+d*2;
					if (PRINTADJ) adjacentcyListFile << (numIps+(numIps/num_layers)*i+plusAddr)*numPorts+1+d*2 << " - " << (numIps+(numIps/num_layers)*i+a)*numPorts+2+d*2 << endl;

				}
				// connection to bus
				ports[(numIps+(numIps/num_layers)*i+a)*numPorts+dimensions*2+1].next = (numIps+numSwitches)*numPorts+a*num_layers+i;
				ports[(numIps+numSwitches)*numPorts+a*num_layers+i].next = (numIps+(numIps/num_layers)*i+a)*numPorts+dimensions*2+1;
				if (PRINTADJ) adjacentcyListFile << (numIps+numSwitches)*numPorts+a*num_layers+i <<  " - " <<(numIps+(numIps/num_layers)*i+a)*numPorts+dimensions*2+1 << endl;
			}
		}

		free (plusAddrRel);
		free (minusAddrRel);
	}

	if (top_type==RING){
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int a=0;a<numIps;a++){
			ports[(numIps+a)*numPorts+1].next = numPorts*(((numIps+a-1)%numIps) + numIps) + 2;  // 1 is the towards the lower numbered switch
			ports[(numIps+a)*numPorts+2].next = numPorts*(((numIps+a+1)%numIps) + numIps) + 1;  // 2 is the towards the lower numbered switch
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts+2 << " - " <<  numPorts*(((numIps+a+1)%numIps) + numIps) + 1 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1)%numIps) + numIps) + 1<< " - " << (numIps+a)*numPorts+2 << endl;
		}
	}

	if (top_type==OCTO){
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int a=0;a<numIps;a++){
			ports[(numIps+a)*numPorts+1].next = numPorts*(((numIps+a-1)%numIps) + numIps) + 2;  // 1 is the towards the lower numbered switch
			ports[(numIps+a)*numPorts+2].next = numPorts*(((numIps+a+1)%numIps) + numIps) + 1;  // 2 is the towards the higher numbered switch
			ports[(numIps+a)*numPorts+3].next = numPorts*(((numIps+a+4)%numIps) + numIps) + 3;	// 3 is across the ring
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts+2 << " - " <<  numPorts*(((numIps+a+1)%numIps) + numIps) + 1 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1)%numIps) + numIps) + 1<< " - " << (numIps+a)*numPorts+2 << endl;
		}
	}

	if (top_type==OCTOM){
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int a=0;a<numIps;a++){
			int ring = (int) a/8;
			ports[(numIps+a)*numPorts+1].next = numPorts*(((a-1)%8) + ring*8 + numIps) + 2;  // 1 is the towards the lower numbered switch
			ports[(numIps+a)*numPorts+2].next = numPorts*(((a+1)%8) + ring*8 + numIps) + 1;  // 2 is the towards the higher numbered switch
			ports[(numIps+a)*numPorts+3].next = numPorts*(((a+4)%8) + ring*8 + numIps) + 3;	// 3 is across the ring
			ports[(numIps+a)*numPorts+4].next = numPorts*(((numIps+a-1*8)%numIps) + numIps) + 5;	// 4 is to lower ring
			ports[(numIps+a)*numPorts+5].next = numPorts*(((numIps+a+1*8)%numIps) + numIps) + 4;	// 5 is to higher ring
			ports[(numIps+a)*numPorts+6].next = numPorts*(((numIps+a+4*8)%numIps) + numIps) + 6;	// 6 is across the ring dim2
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts+2 << " - " <<  numPorts*(((numIps+a+1)%numIps) + numIps) + 1 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1)%numIps) + numIps) + 1<< " - " << (numIps+a)*numPorts+2 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a-1*8)%numIps) + numIps) + 5<< " - " << (numIps+a)*numPorts+4 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1*8)%numIps) + numIps) + 4<< " - " << (numIps+a)*numPorts+5 << endl;
		}
	}

	if (top_type==OCTOM3){
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int a=0;a<numIps;a++){
			int ring_of_8 = (int) a/8;
			int ring_of_64 = (int) a/64;
			ports[(numIps+a)*numPorts+1].next = numPorts*(((a-1)%8) + ring_of_8*8 + numIps) + 2;  // 1 is the towards the lower numbered switch
			ports[(numIps+a)*numPorts+2].next = numPorts*(((a+1)%8) + ring_of_8*8 + numIps) + 1;  // 2 is the towards the higher numbered switch
			ports[(numIps+a)*numPorts+3].next = numPorts*(((a+4)%8) + ring_of_8*8 + numIps) + 3;	// 3 is across the ring
			ports[(numIps+a)*numPorts+4].next = numPorts*(((a-1*8)%64) + ring_of_64*64 + numIps) + 5;	// 4 is to lower ring
			ports[(numIps+a)*numPorts+5].next = numPorts*(((a+1*8)%64) + ring_of_64*64 + numIps) + 4;	// 5 is to higher ring
			ports[(numIps+a)*numPorts+6].next = numPorts*(((a+4*8)%64) + ring_of_64*64 + numIps) + 6;	// 6 is across the ring dim2
			ports[(numIps+a)*numPorts+7].next = numPorts*(((a-1*64)%numIps) + numIps) + 8;	// 4 is to lower ring
			ports[(numIps+a)*numPorts+8].next = numPorts*(((a+1*64)%numIps) + numIps) + 7;	// 5 is to higher ring
			ports[(numIps+a)*numPorts+9].next = numPorts*(((a+4*64)%numIps) + numIps) + 9;	// 6 is across the ring dim2




			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts+2 << " - " <<  numPorts*(((numIps+a+1)%numIps) + numIps) + 1 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1)%numIps) + numIps) + 1<< " - " << (numIps+a)*numPorts+2 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a-1*8)%numIps) + numIps) + 5<< " - " << (numIps+a)*numPorts+4 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1*8)%numIps) + numIps) + 4<< " - " << (numIps+a)*numPorts+5 << endl;
		}
	}

	if (top_type==OCTOM256){
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int a=0;a<numIps;a++){
			int ring_of_8 = (int) a/8;
			int ring_of_64 = (int) a/64;
			ports[(numIps+a)*numPorts+1].next = numPorts*(((a-1)%8) + ring_of_8*8 + numIps) + 2;  // 1 is the towards the lower numbered switch
			ports[(numIps+a)*numPorts+2].next = numPorts*(((a+1)%8) + ring_of_8*8 + numIps) + 1;  // 2 is the towards the higher numbered switch
			ports[(numIps+a)*numPorts+3].next = numPorts*(((a+4)%8) + ring_of_8*8 + numIps) + 3;	// 3 is across the ring
			ports[(numIps+a)*numPorts+4].next = numPorts*(((a-1*8)%64) + ring_of_64*64 + numIps) + 5;	// 4 is to lower ring
			ports[(numIps+a)*numPorts+5].next = numPorts*(((a+1*8)%64) + ring_of_64*64 + numIps) + 4;	// 5 is to higher ring
			ports[(numIps+a)*numPorts+6].next = numPorts*(((a+4*8)%64) + ring_of_64*64 + numIps) + 6;	// 6 is across the ring dim2
			ports[(numIps+a)*numPorts+7].next = numPorts*(((a-1*64)%numIps) + numIps) + 8;	// 4 is to lower ring
			ports[(numIps+a)*numPorts+8].next = numPorts*(((a+1*64)%numIps) + numIps) + 7;	// 5 is to higher ring
			ports[(numIps+a)*numPorts+9].next = numPorts*(((a+2*64)%numIps) + numIps) + 9;	// 6 is across the ring dim2




			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts+2 << " - " <<  numPorts*(((numIps+a+1)%numIps) + numIps) + 1 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1)%numIps) + numIps) + 1<< " - " << (numIps+a)*numPorts+2 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a-1*8)%numIps) + numIps) + 5<< " - " << (numIps+a)*numPorts+4 << endl;
			if (PRINTADJ) adjacentcyListFile << numPorts*(((numIps+a+1*8)%numIps) + numIps) + 4<< " - " << (numIps+a)*numPorts+5 << endl;
		}
	}



	if (top_type==OCTO5){
		for (int a=0;a<36;a++){
			ports[a*numPorts].next = (36+a)*numPorts;
			ports[(36+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (36+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (36+a)*numPorts << " - " << a*numPorts  << endl;

		}
		for (int r = 0; r < 3; r++){
			for (int a=0;a<8;a++){
				ports[(36+a+r*8)*numPorts+1].next = numPorts*(36+((a+8-1)%8) +r*8)+ 2;  // 1 is the towards the lower numbered switch
				ports[(36+a+r*8)*numPorts+2].next = numPorts*(36+((a+8+1)%8) +r*8)+ 1;  // 2 is the towards the higher numbered switch
				ports[(36+a+r*8)*numPorts+3].next = numPorts*(36+((a+8+4)%8) +r*8)+ 3;	// 3 is across the ring
				if (PRINTADJ) adjacentcyListFile << (36+a+r*8)*numPorts+1 << " - " << numPorts*(36+((a+8-1)%8)+r*8)+ 2 << endl;
				if (PRINTADJ) adjacentcyListFile << (36+a+r*8)*numPorts+2 << " - " << numPorts*(36+((a+8+1)%8)+r*8)+ 1 << endl;
				if (PRINTADJ) adjacentcyListFile << (36+a+r*8)*numPorts+3 << " - " << numPorts*(36+((a+8+4)%8)+r*8)+ 3 << endl;
			}	
		}

		ports[numPorts*(36+32)+3].next=numPorts*(36+34)+3;
		ports[numPorts*(36+33)+3].next=numPorts*(36+35)+3;
		ports[numPorts*(36+34)+3].next=numPorts*(36+32)+3;
		ports[numPorts*(36+35)+3].next=numPorts*(36+33)+3;	

		// centre ring, extra ports for gateways
		ports[288].next = numPorts*(36+35)+2;
		ports[numPorts*(36+35)+2].next = 288;
		ports[289].next = numPorts*(36+32)+1;
		ports[numPorts*(36+32)+1].next = 289;
		ports[290].next = numPorts*(36+32)+2;
		ports[numPorts*(36+32)+2].next = 290;
		ports[291].next = numPorts*(36+33)+1;
		ports[numPorts*(36+33)+1].next = 291;
		ports[292].next = numPorts*(36+33)+2;
		ports[numPorts*(36+33)+2].next = 292;
		ports[293].next = numPorts*(36+34)+1;
		ports[numPorts*(36+34)+1].next = 293;
		ports[294].next = numPorts*(36+34)+2;
		ports[numPorts*(36+34)+2].next = 294;
		ports[295].next = numPorts*(36+35)+1;
		ports[numPorts*(36+35)+1].next = 295;

		// straight across in centre ring
		ports[296].next = 298;
		ports[298].next = 296;
		ports[299].next=297;
		ports[297].next=299;

	}

	if (top_type == MESH || top_type == TORUS) {
		for (int a=0;a<numIps;a++){
			ports[a*numPorts].next = (numIps+a)*numPorts;
			ports[(numIps+a)*numPorts].next = a*numPorts;
			if (PRINTADJ) adjacentcyListFile << a*numPorts << " - " <<  (numIps+a)*numPorts << endl;
			if (PRINTADJ) adjacentcyListFile << (numIps+a)*numPorts << " - " << a*numPorts  << endl;

		}
		// do horizontal links, and vertical links
		for (int a=0;a<ynodes;a++){
			for (int b = 0; b < xnodes; b++){
				ports[(numIps+a*xnodes+b)*numPorts+1].next = numPorts*((b-1)%xnodes + a*xnodes + numIps) + 2;  // 1 is the towards the lower numbered switch (xdir)
				ports[(numIps+a*xnodes+b)*numPorts+2].next = numPorts*((b+1)%xnodes + a*xnodes + numIps) + 1;  // 2 is the towards the higher numbered switch (xdir)
				ports[(numIps+a*xnodes+b)*numPorts+3].next = numPorts*(b + ((a-1)%ynodes)*xnodes + numIps) + 4;  // 3 is the towards the lower numbered switch (ydir)
				ports[(numIps+a*xnodes+b)*numPorts+4].next = numPorts*(b + ((a+1)%ynodes)*xnodes + numIps) + 3;  // 4 is the towards the higher numbered switch (ydir)
			}				
		}
	}
}



void reinitialize_network(){
	if (top_type==CUBE) 
		tempAddr = (int*) calloc (dimensions, sizeof(int));
	if (top_type==CLUSTERED || top_type==STACKED) 
		tempAddr = (int*) calloc (dimensions+1, sizeof(int));
	if (top_type==BFT || top_type==KARY) 
		tempAddr = (int*) calloc (levels, sizeof(int));
	if (top_type==SUPERS)
		tempAddr = (int*) calloc(dimensions, sizeof(int));

	maxMessage=2*numNodes*numVirts*(6/5);
	//if (maxMessage<500) maxMessage=4000;
	cout << "maxMessage= " << maxMessage << endl;
	counter=0;
	for (long b=0 ; b < maxMessage; b++){
		msgs[b].end_time=-1;
		msgs[b].header_moved=false;
		msgs[b].header_done=false;
		msgs[b].header_in=false;
	}
	numActiveMsgs = 0;
	firstMsg=-1;
	currentMsg=-1;

	if (top_type==HBUS)
	{
		for (int a = 0; a < 16; a++)
			bus[a]=0; // initalize bus, and crossbar  (0-3) bus content (4,5) crossbar port 1 (in,out)
	}

	for (int c = 0; c < total_num_of_ports; c++)
	{
		to_internode_move_ports[c]=0;
		to_internode_move_oldports[c]=0;
		to_internode_move_flits[c]=0;
		to_internode_move_virts[c]=-1;
		to_internode_move_oldvirts[c]=-1;
		to_intranode_move_ports[c]=0;
		to_intranode_move_flits[c]=0;
		to_intranode_move_virts[c]=-1;
		to_intranode_move_oldvirts[c]=-1;

		for (int r = 0; r < numVirts*bufferDepth; r++)
		{
			ports[c].i_buff[r]=0;
			ports[c].o_buff[r]=0;
		}
		headers[c].currentCollision=-1;
		headers[c].firstCollision=-1;
		headers[c].numRequested=0;
	}

	for (int m=0; m < numIps; m++)
	{
		for (int y=0; y < numVirts; y++)
		{
			ips[m].consume_msgs[y]=0;
			ips[m].consume[y]=0;
			ips[m].generate[y]=0;
			ips[m].generate_msgs[y]=0;
			ips[m].next_arrival=-1;
		}
		for (int y=0; y < queueSize; y++)
			ips[m].queue[y]=-1;
		ips[m].queue_pop=0;
	}
	temp_done=0;
	temp_lat=0;
	temp_internode_local=0;
	temp_internode_mid=0;
	temp_internode_long=0;
	temp_intranode_header_total=0;
	temp_intranode_data_total=0;
	temp_internode_total=0;
	temp_avg_queue_size=0;
	network_latency = 0;
	total_latency=0;
	total_latency0=0;
	total_latency1=0;
	total_latency2=0;
	total_latency3=0;
	messages_done=0;
	messages_done0=0;
	messages_done1=0;
	messages_done2=0;
	messages_done3=0;
	intranode_header_total=0;
	intranode_data_total=0;
	internode_total=0;
	internode_z=0;
	temp_intranode_data_total=0;
	temp_intranode_header_total=0;
	temp_internode_total=0;
	internode_local=0;
	internode_mid=0;
	internode_long=0;
	temp_internode_local=0;
	temp_internode_mid=0;
	temp_internode_long=0;
	avg_queue_size=0;
	temp_avg_queue_size=0;
	counter=0;
	activeMessages=0;
	local_bus_tot=0;
	far_bus_tot=0;
	tr_input=true;
	tr_counter=0;
	tr_msgs=0;
	if (!traceFile.is_open())
		traceFile.open("trace.txt",fstream::in);	
}

// num is the number of switches in the group
void connect_kary_tree(int startnode,int num){
	int k=numPorts/2;
	int numNext = num/k;	// the number of switches in the lower level's groups
	for (int a = 0; a < num; a++){
		for (int p=0; p < k;p++){
			ports[(startnode+a)*numPorts+p].next=(startnode-numSwitches/levels + a%numNext + p*numNext)*numPorts + k + (int)a/numNext;
			ports[(startnode-numSwitches/levels + a%numNext + p*numNext)*numPorts + k + (int)a/numNext].next=(startnode+a)*numPorts+p;
			if (PRINTADJ) cout << (startnode+a)*numPorts+p << " - " << (startnode-numSwitches/levels + a%numNext + p*numNext)*numPorts + k + (int)a/numNext;
		}
	}

	if (num != k){
		for (int b=0; b<k;b++){
			connect_kary_tree(startnode-numSwitches/levels + b*numNext, numNext);
		}
	}

}

int int_rand(int n)
{
	if ( n <= 0 || n > RAND_MAX )
		throw domain_error("Argument out of range");
	const int bucket_size = RAND_MAX / n;
	int a;
	do 
	{
		a = rand() / bucket_size;
	}
	while ( a >= n );

	return a;
}

float float_rand(float n)
{
	if (n<=0 || n>RAND_MAX/4 )
		throw domain_error("Argument out of range: Not an accurate random number");

	return (rand()/(RAND_MAX + 1.0) * n );
}

// this function returns the total manhatten distance between two nodes
int get_cube_dist_mesh(int* c1, int* c2){
	int dist=0;
	for (int a = 0; a< dimensions; a++)
		dist = dist + abs(c1[a]-c2[a]);
	return dist;
}

int get_clustered_dist_mesh(int* c1, int* c2){
	int dist=0;
	for (int a = 0; a<= dimensions; a++)
		dist = dist + abs(c1[a]-c2[a]);
	return dist;
}

int get_stacked_dist_mesh(int* c1, int* c2){
	int dist=0;
	for (int a = 0; a<= dimensions; a++)
		dist = dist + abs(c1[a]-c2[a]);
	return dist;
}

// this function returns the total manhatten distance between two nodes
int get_cube_dist_torus(int* c1, int* c2){
	int dist=0;
	int min, max;

	for (int a = 0; a< dimensions; a++){
		if (c1[a]>c2[a]) {
			max=c1[a];
			min=c2[a];
		}
		else{
			max=c2[a];
			min=c1[a];
		}
		if (min+cube_dimensions[a]-max < abs(c1[a]-c2[a]))
			dist = dist + min+cube_dimensions[a]-max;
		else 
			dist = dist + abs(c1[a]-c2[a]);		
	}
	return dist;
}

int get_cube_address(int* coords){
	//int address=0;
	//for (int a=0; a < dimensions; a++)
	//	address = address + coords[a]*(int)pow((float)maxDim,a);
	//return address;
	int multiplier;
	int address=0;
	for (int a=0; a < dimensions; a++) {
		multiplier=1;
		for (int b=a-1; b>=0 ; b--) {
			multiplier*=cube_dimensions[b];
		}
		address += coords[a]*multiplier;
	}
	//address = address + coords[a]*mypow(cube_dimensions[a],a);
	//address += coords[dimensions];
	return address;
}

int get_clustered_address(int* coords){
	int address=0;
	int multiplier;
	for (int a=dimensions-1; a>=0 ; a--) {
		multiplier=1;
		for (int b=a-1; b>=0 ; b--) {
			multiplier*=cube_dimensions[b];
		}
		address += coords[a]*multiplier*ip_per_switch;
	}
	address += coords[dimensions];
	//for (int a=0; a < dimensions; a++)
	//	address = address + coords[a]*mypow(cube_dimensions[dimensions-a-1],a+1);
	//address += coords[dimensions]*mypow(cube_dimensions[dimensions], dimensions);
	return address;
}

int get_stacked_address(int* coords){
	int address=0;
	for (int a=0; a <= dimensions; a++)
		address = address + coords[a]*(int)pow((float)maxDim,a);
	return address;
}

int get_bft_address(int* coords){
	int address=0;
	for (int a=0; a < levels; a++)
		address = address + coords[a]*((int)pow((float)4,a));
	return address;
}

void get_cube_rel_addr(int address){
	//int *rel_addr;
	int holder=address;
	int denom;
	if (holder>=numIps) holder = holder-numIps; // shift to node coords from switch
	//rel_addr = (int*) calloc (dimensions, sizeof(int));
	//tempAddr = (int*) realloc (tempAddr, dimensions*sizeof(int));
	for (int a = dimensions-1; a >= 0; a--){
		denom=1;
		for(int i=0; i<a; i++) {
			denom *= cube_dimensions[i];
		}
		tempAddr[a]=holder/denom;
		holder = holder-tempAddr[a]*denom;
		//if ((int)holder/((int)pow((float)maxDim,a))>0)  {
		//	tempAddr[a]=(int)holder/((int)pow((float)maxDim,a));
		//	holder = holder-tempAddr[a]*((int)pow((float)maxDim,a));
		//}
		//else  tempAddr[a]=0;		
	}
	//return tempAddr;

}


void get_stacked_rel_addr(int address){
	//int *rel_addr;
	int holder=address;
	if (holder>=numIps) holder = holder-numIps; // shift to node coords from switch
	//rel_addr = (int*) calloc (dimensions, sizeof(int));
	//tempAddr = (int*) realloc (tempAddr, dimensions*sizeof(int));
	for (int a = dimensions; a >= 0; a--){
		if ((int)holder/((int)pow((float)maxDim,a))>0)  {
			tempAddr[a]=(int)holder/((int)pow((float)maxDim,a));
			holder = holder-tempAddr[a]*((int)pow((float)maxDim,a));
		}
		else  tempAddr[a]=0;		
	}
	//return tempAddr;

}

void get_clustered_rel_addr(int address){
	int denom;
	int holder=address;
	if (holder>=numIps){
		holder = holder-numIps; // shift to node coords from switch
		for (int a = dimensions-1; a >= 0; a--){
			denom=1;
			for(int i=0; i<a; i++) {
				denom *= cube_dimensions[i];
			}
			tempAddr[a]=holder/denom;
			holder = holder-tempAddr[a]*denom;
		}
		//for (int a = dimensions-1; a >= 0; a--){
		//	if ((int)holder/((int)pow((float)maxDim,a))>0)  {
		//		tempAddr[a]=(int)holder/((int)pow((float)maxDim,a));
		//		holder = holder-tempAddr[a]*((int)pow((float)maxDim,a));
		//	}
		//	else  tempAddr[a]=0;		
		//}
	}
	else { // this is an IP block
		tempAddr[dimensions] = holder % ip_per_switch;
		holder /= ip_per_switch;
		for(int a=0; a<dimensions; a++){
			tempAddr[a]= holder % cube_dimensions[a];
			holder /= cube_dimensions[a];
		}
	}
}

void get_bft_rel_addr(int address){
	//int *reddr;
	int holder=address;
	//rel_addr = (int*) calloc (levels, sizeof(int));
	for (int a = levels-1; a >= 0; a--){
		if ((int)holder/(int)pow((float)4,a)>0)  {
			tempAddr[a]=(int)holder/(int)pow((float)4,a);
			holder = holder-tempAddr[a]*(int)pow((float)4,a);
		}
		else  tempAddr[a]=0;		
	}
	//return tempAddr;
}

float get_exp_dist(float mean){
	//return (1.0*rand()/(RAND_MAX+1.0));
	return ((float)-mean * log (float_rand(1)));
}

// ***********************OUTPUT FUNCTIONS***********************************
void dump(){
	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << endl;
	for (int a =0; a < numNodes; a++){
		for (int b = 0; b < numPorts; b++){
			outFile << "NODE: " << a << " PORT: " << b << " o: " << ports[a*numPorts + b].o_buff << " i: " << ports[a*numPorts + b].i_buff << endl;

		}
		if (a < numIps)
			outFile << "IP: " << a << " GEN: " << ips[a].generate << " CON: " << ips[a].consume << endl;
	}
}

void printBus(){
	cout << "\nT: " << cycles;
	for (int a = 0; a < 16; a++){
		cout << " " << a << ": " << bus[a];
	}
}
void dump_adjacentcy(){
	outFile << endl << "**** ADJACENTCY LIST ****" << endl;
	for (int a = 0; a < numNodes; a++){
		for (int b = 0; b < numPorts; b++) {
			outFile  << a*numPorts+b << " - " << ports[a*numPorts+b].next << endl;
		}
	}
	outFile << endl << endl;
}

void dump_ports(){

	if (bufferDepth==0){
		int count=0;
		portsFile << "\nT: " << cycles; 
		for	(int a = 0; a < numNodes; a++){
			for (int b = 0; b < numPorts; b++) {
				for (int v=0; v < numVirts; v++){
					portsFile  << " (" << a << "," << b << ")O(" << v << "): "<< ports[a*numPorts + b].o_buff[v];
				}
				for (int v=0; v < numVirts; v++){
					portsFile  << " (" << a << "," << b << ")I(" << v << "): "<< ports[a*numPorts + b].i_buff[v];
				}
				count++;
				if (count==40) {
					portsFile << "\n\t\t";
					count=0;
				}
			}
		}
		if (top_type==OCTO5)
			for (int w=288; w <300; w++)
				portsFile  << " (" << w << ")O: " << ports[w].o_buff[0] << " I: " << ports[w].i_buff[0];
	}

	else {
		int count=0;
		portsFile << "\nT: " << cycles; 
		for (int a = 0; a < numNodes; a++){
			for (int b = 0; b < numPorts; b++) {
				for (int v=0; v < numVirts*bufferDepth; v++){
					portsFile  << " (" << a << "," << b << ")O(" << v << "): "<< ports[a*numPorts + b].o_buff[v];
				}
				for (int v=0; v < numVirts*bufferDepth; v++){
					portsFile  << " (" << a << "," << b << ")I(" << v << "): "<< ports[a*numPorts + b].i_buff[v];
				}
				count++;
				if (count==40) {
					portsFile << "\n\t\t";
					count=0;
				}
			}
		}
	}
}

void dump_gateways(){
	if (cycles==0)
		gateFile << "T;(36,0)O;(36,0)i;(36,1)O;(36,1)i;(36,2)O;(36,2)i;(36,3)O;(36,3)i;(288,->71)O;(288,->71)i;(289,->68)O;(289,->68)i;(296,->52)O;(296,->52)i;;"
		<< "(44,0)O;(44,0)i;(44,1)O;(44,1)i;(44,2)O;(44,2)i;(44,3)O;(44,3)i;(290,->68)O;(290->68)i;(291,->69)O;(291,->69)i;(297,->60)O;(297,->60)i;;"
		<< "(52,0)O;(52,0)i;(52,1)O;(52,1)i;(52,2)O;(52,2)i;(52,3)O;(52,3)i;(292,->69)O;(292->69)i;(293,->70)O;(293,->70)i;(298,->36)O;(298,->36)i;;"
		<< "(60,0)O;(60,0)i;(60,1)O;(60,1)i;(60,2)O;(60,2)i;(60,3)O;(60,3)i;(294,->70)O;(294->70)i;(295,->71)O;(295,->71)i;(299,->44)O;(299,->44)i;;\n";
	gateFile << cycles << ";" << ports[36*numPorts+0].o_buff[0] << ";" << ports[36*numPorts+0].i_buff[0] << ";"
		<< ports[36*numPorts+1].o_buff[0] << ";" << ports[36*numPorts+1].i_buff[0] << ";"
		<< ports[36*numPorts+2].o_buff[0] << ";" << ports[36*numPorts+2].i_buff[0] << ";"
		<< ports[36*numPorts+3].o_buff[0] << ";" << ports[36*numPorts+3].i_buff[0] << ";";
	gateFile << ports[288].o_buff[0] << ";" << ports[288].i_buff[0] << ";"
		<< ports[289].o_buff[0] << ";" << ports[289].i_buff[0] << ";"
		<< ports[296].o_buff[0] << ";" << ports[296].i_buff[0] << ";;";
	gateFile << ports[44*numPorts+0].o_buff[0] << ";" << ports[44*numPorts+0].i_buff[0] << ";"
		<< ports[44*numPorts+1].o_buff[0] << ";" << ports[44*numPorts+1].i_buff[0] << ";"
		<< ports[44*numPorts+2].o_buff[0] << ";" << ports[44*numPorts+2].i_buff[0] << ";"
		<< ports[44*numPorts+3].o_buff[0] << ";" << ports[44*numPorts+3].i_buff[0] << ";";
	gateFile << ports[290].o_buff[0] << ";" << ports[290].i_buff[0] << ";"
		<< ports[291].o_buff[0] << ";" << ports[291].i_buff[0] << ";"
		<< ports[297].o_buff[0] << ";" << ports[297].i_buff[0] << ";;";
	gateFile << ports[52*numPorts+0].o_buff[0] << ";" << ports[52*numPorts+0].i_buff[0] << ";"
		<< ports[52*numPorts+1].o_buff[0] << ";" << ports[52*numPorts+1].i_buff[0] << ";"
		<< ports[52*numPorts+2].o_buff[0] << ";" << ports[52*numPorts+2].i_buff[0] << ";"
		<< ports[52*numPorts+3].o_buff[0] << ";" << ports[52*numPorts+3].i_buff[0] << ";";
	gateFile << ports[292].o_buff[0] << ";" << ports[292].i_buff[0] << ";"
		<< ports[293].o_buff[0] << ";" << ports[293].i_buff[0] << ";"
		<< ports[298].o_buff[0] << ";" << ports[298].i_buff[0] << ";;";
	gateFile << ports[60*numPorts+0].o_buff[0] << ";" << ports[60*numPorts+0].i_buff[0] << ";"
		<< ports[60*numPorts+1].o_buff[0] << ";" << ports[60*numPorts+1].i_buff[0] << ";"
		<< ports[60*numPorts+2].o_buff[0] << ";" << ports[60*numPorts+2].i_buff[0] << ";"
		<< ports[60*numPorts+3].o_buff[0] << ";" << ports[60*numPorts+3].i_buff[0] << ";";
	gateFile << ports[294].o_buff[0] << ";" << ports[294].i_buff[0] << ";"
		<< ports[295].o_buff[0] << ";" << ports[295].i_buff[0] << ";"
		<< ports[299].o_buff[0] << ";" << ports[299].i_buff[0] << endl;
}


void print5() {
	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << endl;
	outFile << "\t" << ports[4*numPorts+0].i_buff[0] << "\t" << ports[4*numPorts+0].i_buff[1] << " i|o " << ports[4*numPorts+0].o_buff[0] << "\t" << ports[4*numPorts+0].o_buff[1]
	<< "\t\t" << ports[4*numPorts+1].i_buff[0] << "\t" << ports[4*numPorts+1].i_buff[1] << " i|o " << ports[4*numPorts+1].o_buff[0] << "\t" << ports[4*numPorts+1].o_buff[1]
	<< "\t\t" << ports[4*numPorts+2].i_buff[0] << "\t" << ports[4*numPorts+2].i_buff[1] << " i|o " << ports[4*numPorts+2].o_buff[0] << "\t" << ports[4*numPorts+2].o_buff[1]
	<< "\t\t" << ports[4*numPorts+3].i_buff[0] << "\t" << ports[4*numPorts+3].i_buff[1] << " i|o " << ports[4*numPorts+3].o_buff[0] << "\t" << ports[4*numPorts+3].o_buff[1] << endl;

	outFile << "\t" << ports[0*numPorts+4].o_buff[0] << "\t" << ports[0*numPorts+4].o_buff[1] << " o|i " << ports[0*numPorts+4].i_buff[0] << "\t" << ports[0*numPorts+4].i_buff[1]
	<< "\t\t" << ports[1*numPorts+4].o_buff[0] << "\t" << ports[1*numPorts+4].o_buff[1] << " o|i " << ports[1*numPorts+4].i_buff[0] << "\t" << ports[1*numPorts+4].i_buff[1]
	<< "\t\t" << ports[2*numPorts+4].o_buff[0] << "\t" << ports[2*numPorts+4].o_buff[1] << " o|i " << ports[2*numPorts+4].i_buff[0] << "\t" << ports[2*numPorts+4].i_buff[1]
	<< "\t\t" << ports[3*numPorts+4].o_buff[0] << "\t" << ports[3*numPorts+4].o_buff[1] << " o|i " << ports[3*numPorts+4].i_buff[0] << "\t" << ports[3*numPorts+4].i_buff[1] << endl;

	outFile << "\n\t" << ips[0].generate[0] << " " << ips[0].generate[1] 
	<< "\t" << ips[1].generate[0] << " " << ips[1].generate[1] 
	<< "\t" << ips[2].generate[0] << " " << ips[2].generate[1] 
	<< "\t" << ips[3].generate[0] << " " << ips[3].generate[1] << endl;

	outFile << "\t" << ips[0].consume[0] << " " << ips[0].consume[1] 
	<< "\t" << ips[1].consume[0] << " " << ips[1].consume[1] 
	<< "\t" << ips[2].consume[0] << " " << ips[2].consume[1] 
	<< "\t" << ips[3].consume[0] << " " << ips[3].consume[1] << endl;

}

// to be call once to head file
void printRingHeader(){
	outFile << ";";
	for (int a =0; a < numNodes; a++)
		for (int b=0; b < numPorts; b++) {
			outFile << "(" << a << "," << b << "i);";
			outFile << "(" << a << "," << b << "o);";
		}
		outFile << endl;
}


void printRing(){
	outFile << "\nt " << cycles << ";";
	for (int a=numIps*numPorts; a < numPorts*numNodes; a++){
		for (int b=0; b < numVirts; b++){
			outFile << ports[a].i_buff[b] << ";";
		}
		for (int c=0; c < numVirts; c++){
			outFile << ports[a].o_buff[c] << ";";
		}
	}
	outFile << endl << "t " << cycles << ";";

	for (int a=0; a < numIps*numPorts; a++){
		for (int b=0; b < numVirts; b++){
			outFile << ports[a].i_buff[b] << ";";
		}
		for (int c=0; c < numVirts; c++){
			outFile << ports[a].o_buff[c] << ";";
		}
	}	
}

// to be call once to head file
void printOctoHeader(){
	outFile << ";";
	for (int a =0; a < numNodes; a++)
		for (int b=0; b < numPorts; b++) {
			outFile << "(" << a << "," << b << "i);";
			outFile << "(" << a << "," << b << "o);";
		}
		outFile << endl;
}


void printOcto(){
	outFile << "\nt " << cycles << ";";
	for (int a=numIps*numPorts; a < numPorts*numNodes; a++){
		for (int b=0; b < numVirts; b++){
			outFile << ports[a].i_buff[b] << ";";
		}
		for (int c=0; c < numVirts; c++){
			outFile << ports[a].o_buff[c] << ";";
		}
	}
	outFile << endl << "t " << cycles << ";";

	for (int a=0; a < numIps*numPorts; a++){
		for (int b=0; b < numVirts; b++){
			outFile << ports[a].i_buff[b] << ";";
		}
		for (int c=0; c < numVirts; c++){
			outFile << ports[a].o_buff[c] << ";";
		}
	}	
}


void print12() {
	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << endl;
	outFile << "\t" << ports[10*numPorts+0].i_buff << " i|o " << ports[10*numPorts+0].o_buff
		<< "\t\t" << ports[10*numPorts+1].i_buff << " i|o " << ports[10*numPorts+1].o_buff
		<< "\t\t\t10 |*| 11\t\t\t" << ports[11*numPorts+0].i_buff << " i|o " << ports[11*numPorts+0].o_buff
		<< "\t\t" << ports[11*numPorts+1].i_buff << " i|o " << ports[11*numPorts+1].o_buff << endl;

	outFile << "\t" << ports[8*numPorts+4].o_buff << " o|i " << ports[8*numPorts+4].i_buff
		<< "\t\t" << ports[8*numPorts+5].o_buff << " o|i " << ports[8*numPorts+5].i_buff
		<< "\t\t\t8  |*|  9\t\t\t" << ports[9*numPorts+4].o_buff << " o|i " << ports[9*numPorts+4].i_buff
		<< "\t\t" << ports[9*numPorts+5].o_buff << " o|i " << ports[9*numPorts+5].i_buff << endl;

	outFile << ports[8*numPorts+0].i_buff << " i|o " << ports[8*numPorts+0].o_buff
		<< "\t" << ports[8*numPorts+1].i_buff << " i|o " << ports[8*numPorts+1].o_buff
		<< "\t" << ports[8*numPorts+2].i_buff << " i|o " << ports[8*numPorts+2].o_buff
		<< "\t" << ports[8*numPorts+3].i_buff << " i|o " << ports[8*numPorts+3].o_buff

		<< "\t 8 |*| 9 \t" << ports[9*numPorts+0].i_buff << " i|o " << ports[9*numPorts+0].o_buff
		<< "\t" << ports[9*numPorts+1].i_buff << " i|o " << ports[9*numPorts+1].o_buff
		<< "\t" << ports[9*numPorts+2].i_buff << " i|o " << ports[9*numPorts+2].o_buff
		<< "\t" << ports[9*numPorts+3].i_buff << " i|o " << ports[9*numPorts+3].o_buff << endl;

	outFile << ports[0*numPorts+4].o_buff << " o|i " << ports[0*numPorts+4].i_buff
		<< "\t" << ports[1*numPorts+4].o_buff << " o|i " << ports[1*numPorts+4].i_buff
		<< "\t" << ports[2*numPorts+4].o_buff << " o|i " << ports[2*numPorts+4].i_buff
		<< "\t" << ports[3*numPorts+4].o_buff << " o|i " << ports[3*numPorts+4].i_buff

		<< "\t 0-3|*|4-7 \t" << ports[4*numPorts+4].o_buff << " o|i " << ports[4*numPorts+4].i_buff
		<< "\t" << ports[5*numPorts+4].o_buff << " o|i " << ports[5*numPorts+4].i_buff
		<< "\t" << ports[6*numPorts+4].o_buff << " o|i " << ports[6*numPorts+4].i_buff
		<< "\t" << ports[7*numPorts+4].o_buff << " o|i " << ports[7*numPorts+4].i_buff	<< endl;
}

void print22() {
	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << endl;
	outFile << "\t" << ports[20*numPorts+0].i_buff[0]  << "\t " << ports[20*numPorts+0].i_buff[1]  << " i|o " << ports[20*numPorts+0].o_buff[0] << "\t " << ports[20*numPorts+0].o_buff[1]
	<< "\t\t" << ports[20*numPorts+1].i_buff[0] << "\t " << ports[20*numPorts+1].i_buff[1]  << " i|o " << ports[20*numPorts+1].o_buff[0] << "\t " << ports[20*numPorts+1].o_buff[1]
	<< "\t\t" << ports[20*numPorts+2].i_buff[0] << "\t " << ports[20*numPorts+2].i_buff[1]  << " i|o " << ports[20*numPorts+2].o_buff[0] << "\t " << ports[20*numPorts+2].o_buff[1]
	<< "\t\t" << ports[20*numPorts+3].i_buff[0] << "\t " << ports[20*numPorts+3].i_buff[1]  << " i|o " << ports[20*numPorts+3].o_buff[0] << "\t " << ports[20*numPorts+3].o_buff[1]
	<< "\t\t\t\t\t\t\t\t\t\t" << ports[21*numPorts+0].i_buff[0] << "\t " << ports[21*numPorts+0].i_buff[1] << " i|o " << ports[21*numPorts+0].o_buff[0] << " " << ports[21*numPorts+0].o_buff[1]
	<< "\t\t" << ports[21*numPorts+1].i_buff[0] << "\t " << ports[21*numPorts+1].i_buff[1] << " i|o " << ports[21*numPorts+1].o_buff[0] << "\t " << ports[21*numPorts+1].o_buff[1]
	<< "\t\t" << ports[21*numPorts+2].i_buff[0] << "\t " << ports[21*numPorts+2].i_buff[1] << " i|o " << ports[21*numPorts+2].o_buff[0] << "\t " << ports[21*numPorts+2].o_buff[1]
	<< "\t\t" << ports[21*numPorts+3].i_buff[0] << "\t " << ports[21*numPorts+3].i_buff[1] << " i|o " << ports[21*numPorts+3].o_buff[0] << "\t " << ports[21*numPorts+3].o_buff[1] << endl;


	outFile << "\t" << ports[16*numPorts+4].o_buff[0] << "\t " << ports[16*numPorts+4].o_buff[1] << " o|i " << ports[16*numPorts+4].i_buff[0] << "\t " << ports[16*numPorts+4].i_buff[1]
	<< "\t\t" << ports[16*numPorts+5].o_buff[0] << "\t " << ports[16*numPorts+5].o_buff[1]  << " o|i " << ports[16*numPorts+5].i_buff[0] << "\t " << ports[16*numPorts+5].i_buff[1]
	<< "\t\t\t\t\t\t" << ports[17*numPorts+4].o_buff[0] << "\t " << ports[17*numPorts+4].o_buff[1]  << " o|i " << ports[17*numPorts+4].i_buff[0] << "\t " << ports[17*numPorts+4].i_buff[1]
	<< "\t\t" << ports[17*numPorts+5].o_buff[0] << "\t " << ports[17*numPorts+5].o_buff[1]  << " o|i " << ports[17*numPorts+5].i_buff[0] << "\t " << ports[17*numPorts+5].i_buff[1]
	<< "\t\t\t\t\t\t" << ports[18*numPorts+4].o_buff[0] << "\t " << ports[18*numPorts+4].o_buff[1]  << " o|i " << ports[18*numPorts+4].i_buff[0] << "\t " << ports[18*numPorts+4].i_buff[1]
	<< "\t\t" << ports[18*numPorts+5].o_buff[0] << "\t " << ports[18*numPorts+5].o_buff[1]  << " o|i " << ports[18*numPorts+5].i_buff[0] << "\t " << ports[18*numPorts+5].i_buff[1]
	<< "\t\t\t\t\t\t" << ports[19*numPorts+4].o_buff[0] << " " << ports[19*numPorts+4].o_buff[1]  << " o|i " << ports[19*numPorts+4].i_buff[0] << "\t " << ports[19*numPorts+4].i_buff[1]
	<< "\t\t" << ports[19*numPorts+5].o_buff[0] << "\t " << ports[19*numPorts+5].o_buff[1]  << " o|i " << ports[19*numPorts+5].i_buff[0]  << "\t " << ports[19*numPorts+5].i_buff[1] << endl;

	outFile << ports[16*numPorts+0].i_buff[0] << "\t " << ports[16*numPorts+0].i_buff[1] << " i|o " << ports[16*numPorts+0].o_buff[0] << "\t " << ports[16*numPorts+0].o_buff[1]
	<< "\t" << ports[16*numPorts+1].i_buff[0] << "\t " << ports[16*numPorts+1].i_buff[1] << " i|o " << ports[16*numPorts+1].o_buff[0] << "\t" << ports[16*numPorts+1].o_buff[1]
	<< "\t" << ports[16*numPorts+2].i_buff[0] << "\t " << ports[16*numPorts+2].i_buff[1] << " i|o " << ports[16*numPorts+2].o_buff[0] << "\t " << ports[16*numPorts+2].o_buff[1]
	<< "\t" << ports[16*numPorts+3].i_buff[0] << "\t " << ports[16*numPorts+3].i_buff[1] << " i|o " << ports[16*numPorts+3].o_buff[0] << "\t " << ports[16*numPorts+3].o_buff[1]

	<< "\t\t" << ports[17*numPorts+0].i_buff[0] << "\t " << ports[17*numPorts+0].i_buff[1] << " i|o " << ports[17*numPorts+0].o_buff[0] << "\t " << ports[17*numPorts+0].o_buff[1]
	<< "\t" << ports[17*numPorts+1].i_buff[0] << "\t " << ports[17*numPorts+1].i_buff[1] << " i|o " << ports[17*numPorts+1].o_buff[0] << "\t " << ports[17*numPorts+1].o_buff[1]
	<< "\t" << ports[17*numPorts+2].i_buff[0] << "\t " << ports[17*numPorts+2].i_buff[1] << " i|o " << ports[17*numPorts+2].o_buff[0] << "\t " << ports[17*numPorts+2].o_buff[1]
	<< "\t" << ports[17*numPorts+3].i_buff[0] << "\t " << ports[17*numPorts+3].i_buff[1] << " i|o " << ports[17*numPorts+3].o_buff[0] << "\t " << ports[17*numPorts+3].o_buff[1]

	<< "\t\t" << ports[18*numPorts+0].i_buff[0] << "\t " << ports[18*numPorts+0].i_buff[1] << " i|o " << ports[18*numPorts+0].o_buff[0] << "\t " << ports[18*numPorts+0].o_buff[1]
	<< "\t" << ports[18*numPorts+1].i_buff[0] << "\t " << ports[18*numPorts+1].i_buff[1] << " i|o " << ports[18*numPorts+1].o_buff[0] << "\t " << ports[18*numPorts+1].o_buff[1]
	<< "\t" << ports[18*numPorts+2].i_buff[0] << "\t " << ports[18*numPorts+2].i_buff[1] << " i|o " << ports[18*numPorts+2].o_buff[0] << "\t " << ports[18*numPorts+2].o_buff[1]
	<< "\t" << ports[18*numPorts+3].i_buff[0] << "\t " << ports[18*numPorts+3].i_buff[1] << " i|o " << ports[18*numPorts+3].o_buff[0] << "\t " << ports[18*numPorts+3].o_buff[1]

	<< "\t\t" << ports[19*numPorts+0].i_buff[0] << "\t " << ports[19*numPorts+0].i_buff[1] << " i|o " << ports[19*numPorts+0].o_buff[0] << "\t " << ports[19*numPorts+0].o_buff[1]
	<< "\t" << ports[19*numPorts+1].i_buff[0] << "\t " << ports[19*numPorts+1].i_buff[1] << " i|o " << ports[19*numPorts+1].o_buff[0] << "\t " << ports[19*numPorts+1].o_buff[1]
	<< "\t" << ports[19*numPorts+2].i_buff[0] << "\t " << ports[19*numPorts+2].i_buff[1] << " i|o " << ports[19*numPorts+2].o_buff[0] << "\t " << ports[19*numPorts+2].o_buff[1]
	<< "\t" << ports[19*numPorts+3].i_buff[0] << "\t " << ports[19*numPorts+3].i_buff[1] << " i|o " << ports[19*numPorts+3].o_buff[0] << "\t " << ports[19*numPorts+3].o_buff[1] << endl;

	outFile << ports[0*numPorts+4].o_buff[0] << "\t " << ports[0*numPorts+4].o_buff[1] << " o|i " << ports[0*numPorts+4].i_buff[0] << "\t " << ports[0*numPorts+4].i_buff[1]
	<< "\t" << ports[1*numPorts+4].o_buff[0] << "\t " << ports[1*numPorts+4].o_buff[1] << " o|i " << ports[1*numPorts+4].i_buff[0] << "\t " << ports[1*numPorts+4].i_buff[1]
	<< "\t" << ports[2*numPorts+4].o_buff[0] << "\t " << ports[2*numPorts+4].o_buff[1] << " o|i " << ports[2*numPorts+4].i_buff[0] << "\t " << ports[2*numPorts+4].i_buff[1]
	<< "\t" << ports[3*numPorts+4].o_buff[0] << "\t " << ports[3*numPorts+4].o_buff[1] << " o|i " << ports[3*numPorts+4].i_buff[0] << "\t " << ports[3*numPorts+4].i_buff[1]

	<< "\t\t" << ports[4*numPorts+4].o_buff[0] << "\t " << ports[4*numPorts+4].o_buff[1] << " o|i " << ports[4*numPorts+4].i_buff[0] << "\t " << ports[4*numPorts+4].i_buff[1]
	<< "\t" << ports[5*numPorts+4].o_buff[0] << "\t " << ports[5*numPorts+4].o_buff[1] << " o|i " << ports[5*numPorts+4].i_buff[0] << "\t " << ports[5*numPorts+4].i_buff[1]
	<< "\t" << ports[6*numPorts+4].o_buff[0] << "\t " << ports[6*numPorts+4].o_buff[1] << " o|i " << ports[6*numPorts+4].i_buff[0] << "\t " << ports[6*numPorts+4].i_buff[1]
	<< "\t" << ports[7*numPorts+4].o_buff[0] << "\t " << ports[7*numPorts+4].o_buff[1] << " o|i " << ports[7*numPorts+4].i_buff[0] << "\t " << ports[7*numPorts+4].i_buff[1]

	<< "\t\t" << ports[8*numPorts+4].o_buff[0] << "\t " << ports[8*numPorts+4].o_buff[1] << " o|i " << ports[8*numPorts+4].i_buff[0] << "\t " << ports[8*numPorts+4].i_buff[1]
	<< "\t" << ports[9*numPorts+4].o_buff[0] << "\t " << ports[9*numPorts+4].o_buff[1] << " o|i " << ports[9*numPorts+4].i_buff[0] << "\t " << ports[9*numPorts+4].i_buff[1]
	<< "\t" << ports[10*numPorts+4].o_buff[0] << "\t " << ports[10*numPorts+4].o_buff[1] << " o|i " << ports[10*numPorts+4].i_buff[0] << "\t " << ports[10*numPorts+4].i_buff[1]
	<< "\t" << ports[11*numPorts+4].o_buff[0] << "\t " << ports[11*numPorts+4].o_buff[1] << " o|i " << ports[11*numPorts+4].i_buff[0] << "\t " << ports[11*numPorts+4].i_buff[1]

	<< "\t\t" << ports[12*numPorts+4].o_buff[0] << "\t " << ports[12*numPorts+4].o_buff[1] << " o|i " << ports[12*numPorts+4].i_buff[0] << "\t " << ports[12*numPorts+4].i_buff[1]
	<< "\t" << ports[13*numPorts+4].o_buff[0] << "\t " << ports[13*numPorts+4].o_buff[1] << " o|i " << ports[13*numPorts+4].i_buff[0] << "\t " << ports[13*numPorts+4].i_buff[1]
	<< "\t" << ports[14*numPorts+4].o_buff[0] << "\t " << ports[14*numPorts+4].o_buff[1] << " o|i " << ports[14*numPorts+4].i_buff[0] << "\t " << ports[14*numPorts+4].i_buff[1]
	<< "\t" << ports[15*numPorts+4].o_buff[0] << "\t " << ports[15*numPorts+4].o_buff[1] << " o|i " << ports[15*numPorts+4].i_buff[0] << "\t " << ports[15*numPorts+4].i_buff[1] << endl;
}

void print24(){
	// print out for 4-ary 2-tree
	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << "token: " << token << " port token: " << port_token<< endl << endl;
	//level 2 child ports
	for (int n = 20; n < 24; n++){
		for (int a = 0; a<4; a++){
			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+a].i_buff[v*bufferDepth+x] << ";";
				}
			}
			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+a].o_buff[v*bufferDepth+x] << ";";
				}
			}
		}
	}
	outFile << endl;	

	//level 1 parent ports
	for (int n = 16; n < 20; n++){
		for (int a = 0; a<4; a++){

			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+4+a].o_buff[v*bufferDepth+x] << ";";
				}
			}
			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+4+a].i_buff[v*bufferDepth+x] << ";";
				}
			}

		}
	}
	outFile << endl;			

	// level 1 child ports
	for (int n = 16; n < 20; n++){
		for (int a = 0 ; a<4; a++){
			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+a].i_buff[v*bufferDepth+x] << ";";
				}
			}
			for (int v= 0; v < numVirts; v++){
				for (int x=0; x < bufferDepth; x++){
					outFile << ports[n*numPorts+a].o_buff[v*bufferDepth+x] << ";";
				}
			}
		}
	}
	outFile << endl;

	// print level 0 parent ports
	for (int n = 0; n < numIps; n++){
		for (int v= 0; v < numVirts; v++){
			for (int x=0; x < bufferDepth; x++){
				outFile << ports[n*numPorts+4].o_buff[v*bufferDepth+x] << ";";
			}
		}
		for (int v= 0; v < numVirts; v++){
			for (int x=0; x < bufferDepth; x++){
				outFile << ports[n*numPorts+4].i_buff[v*bufferDepth+x] << ";";
			}
		}
	}
	outFile << endl;

}

void print92(){

	outFile << "\n\n***** TIME: " << cycles << " *****" << endl << "token: " << token << " port token: " << port_token<< endl << endl;
	//level 3 child ports
	for (int n = 88; n < 92; n++){
		for (int a = 0; a<4; a++){
			outFile << ";;;";
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].i_buff[v] << ";";
			}
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].o_buff[v] << ";";
			}
			outFile << ";;;";
		}
	}
	outFile << endl;	

	//level 2 parent ports
	for (int n = 80; n < 88; n++){
		for (int a = 0; a<2; a++){
			outFile << ";;;";
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a+4].o_buff[v] << ";";
			}
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a+4].i_buff[v] << ";";
			}
			outFile << ";;;";
		}
	}
	outFile << endl;	

	//level 2 child ports
	for (int n = 80; n < 88; n++){
		for (int a = 0; a<4; a++){
			outFile << ";";
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].i_buff[v] << ";";
			}
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].o_buff[v] << ";";
			}
			outFile << ";";
		}
	}
	outFile << endl;	

	//level 1 parent ports
	for (int n = 64; n < 80; n++){
		for (int a = 0; a<2; a++){
			outFile << ";";
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+4+a].o_buff[v] << ";";
			}
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+4+a].i_buff[v] << ";";
			}
			outFile << ";";
		}
	}
	outFile << endl;	

	// level 1 child ports
	for (int n = 64; n < 80; n++){
		for (int a = 0 ; a<4; a++){
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].i_buff[v] << ";";
			}
			for (int v= 0; v < numVirts; v++){
				outFile << ports[n*numPorts+a].o_buff[v] << ";";
			}
		}
	}
	outFile << endl;	


	// print level 0 parent ports
	for (int n = 0; n < numIps; n++){
		for (int v= 0; v < numVirts; v++){
			outFile << ports[n*numPorts+4].o_buff[v] << ";";
		}
		for (int v= 0; v < numVirts; v++){
			outFile << ports[n*numPorts+4].i_buff[v] << ";";
		}
	}
	outFile << endl;
}
// ************************FLIT TRAFFIC FUNCTIONS************************************


void set_bus_moves(){

	// 1a move from buses to nodes if on right bus
	for (int a = 0; a <4 ; a++){
		// there's something in the bus
		if (bus[a]>0) {
			if (msgs[bus[a]%maxMessage].dest[0]/ips_per_bus == a) {	// if this is the appropriate bus
				if (ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]==0 || ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]==-bus[a]%maxMessage){ // it's free, or reserved by this msg
					// so move it in
					ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]=bus[a];
					// and leave a token, unless this is a tail flit
					if (bus[a]<2*maxMessage && bus[a]>maxMessage) bus[a]=0;
					else bus[a]=-bus[a]%maxMessage;
				}
			}
		}
	}
	// 1b move from downward buses to nodes
	for (int a = 12; a <16 ; a++){
		// there's something in the bus
		if (bus[a]>0) {
			if (msgs[bus[a]%maxMessage].dest[0]/ips_per_bus == a-12) {	// if this is the appropriate bus
				if (ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]==0 || ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]==-bus[a]%maxMessage){ // it's free, or reserved by this msg
					// so move it in
					ports[msgs[bus[a]%maxMessage].dest[0]].i_buff[0]=bus[a];
					// and leave a token, unless this is a tail flit
					if (bus[a]<2*maxMessage && bus[a]>maxMessage) bus[a]=0;
					else bus[a]=-bus[a]%maxMessage;
				}
			}
		}
	}
	// 2 move from out ports of crossbar to appropriate bus
	for (int a = 0; a < 4; a++){
		if (bus[5+a*2]>0) {  // there's something in the port
			if(bus[12+a]==0 || bus[12+a]==-bus[5+a*2]%maxMessage){  // if it's free or reserved for this msg
				// so move in
				bus[12+a]=bus[5+a*2];
				// and leave a token, unless this is a tail flit
				if (bus[12+a]<2*maxMessage && bus[12+a]>maxMessage) bus[5+a*2]=0;
				else bus[5+a*2]=-bus[12+a]%maxMessage;
			}
		}
	}
	// 3 process crossbar inport to outport moves
	for (int a =0; a < 4; a++){
		int d=-1;	// destination of current port
		if (bus[4+2*a]>0 ) {

			d = msgs[bus[4+2*a]%maxMessage].dest[0]/ips_per_bus;
			// now check availability
			if (bus[5+2*d]==0 || bus[5+2*d]==-bus[4+2*a]%maxMessage) {	// it's free or reserved by this msg
				// so move in
				bus[5+2*d]=bus[4+2*a];
				// and leave a token, unless this is a tail flit
				if (bus[4+2*a]<2*maxMessage && bus[4+2*a]>maxMessage) bus[4+2*a]=0;
				else bus[4+2*a]=-bus[4+2*a]%maxMessage;
			}
		}
	}
	// 4 move flits from wrong buses to input ports of the crossbar
	for (int a = 0; a < 4; a++){
		if (bus[a]>0) {
			if (msgs[bus[a]%maxMessage].dest[0]/ips_per_bus != a) {	// if this is not the appropriate bus
				if (bus[4+2*a]==0 || bus[4+2*a]==-bus[a]%maxMessage){ // it's free, or reserved by this msg
					// so move it in
					bus[4+2*a]=bus[a];
					// and leave a token, unless this is a tail flit
					if (bus[a]<2*maxMessage && bus[a]>maxMessage) bus[a]=0;
					else bus[a]=-bus[a]%maxMessage;
				}
			}
		}
	}
	// 5 inject to bus from nodes output ports
	for (int a = 0; a < numIps; a++){
		if (ports[a].o_buff[0]>0 ){	// there's something to process
			if(bus[a/ips_per_bus]==0 || bus[a/ips_per_bus]==-ports[a].o_buff[0]%maxMessage){  // it's free or reserved by this msg
				// so move in
				bus[a/ips_per_bus]=ports[a].o_buff[0];
				// and leave a token, unless this is a tail flit
				if (ports[a].o_buff[0]<2*maxMessage && ports[a].o_buff[0]>maxMessage) ports[a].o_buff[0]=0;
				else ports[a].o_buff[0]=-ports[a].o_buff[0]%maxMessage;
			}
		}	
	}
}


// Scan through all ports, check if output buffers are full.
// If so, check if the input buffers of the next node have 
// flits belonging to the same msg as the flit in the output
// buffer.  If not, and there is an empty buffer, advance the 
// flit token.

void set_internode_moves(int start_node, int stop_node, int start_port, int stop_port){
	bool ok = true;
	bool doneThisVirt = false;
	bool allEmpty = false;
	int emptySpace = -1; // stores empty buffer space in case where real measage flits are in the buffer
	int v = 0;  // current virtual channel being serviced
	int buff = 0; // current buffer being serviced
	int type = -1; // 0 = header, 1 = data, 2 = tail, -1 = none
	int node_limit;


	if (top_type==OCTO5) 
		node_limit=numNodes+3;	// to scan extra ports of gateways
	else 
		node_limit = numNodes;

	for (int a =start_node; a <= stop_node; a++)
	{
		for (int b = start_port; b <= stop_port; b++)
		{
			for (int c =0; c < numVirts; c++)
			{
				doneThisVirt = false;
				if (ports[a*numPorts +b].sent_this_cycle!=true)
				{
					type = -1;
					v = (ports[a*numPorts +b].last_virt_sent+1+c)%numVirts;

					// search for header flits, then data, then tail to keep order
					for (int w = 0; w < bufferDepth; w++)
					{
						if (ports[a*numPorts + b].o_buff[v*bufferDepth+w]>2*maxMessage)
						{	// header flit found
							type = 0;
							buff = v*bufferDepth+w;
							w = bufferDepth +10;  // to exit loop
						}
					}
					if (type==-1)
					{
						for (int z = 0; z < bufferDepth; z++)
						{
							if (ports[a*numPorts + b].o_buff[v*bufferDepth+z]>0 && ports[a*numPorts + b].o_buff[v*bufferDepth+z]<maxMessage)
							{	// data flit found
								type = 1;	// data
								buff = v*bufferDepth+z;
								z = bufferDepth +10;  // to exit loop
							}
						}
					}
					if (type==-1)
					{
						for (int y = 0; y < bufferDepth; y++)
						{
							if (ports[a*numPorts + b].o_buff[v*bufferDepth+y]>maxMessage)
							{	// tail flit found
								type = 2; // tail
								buff = v*bufferDepth+y;
								y = bufferDepth +10;  // to exit loop
							}
						}
					}

					if(type != -1)
					{
						if(msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].wait != -1)
						{
							if(type == 1 && (a*numPorts+b) == msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].path[msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].path_length-2])
							{
								type = -1;
							}
							else if (type == 0)
							{
								type = -1;
							}
						}
					}

					// there is a flit to send, look for a destination buffer
					if (type != -1) 
					{  
						if(!fLASH && !fMPLASH && !fALASH)
						{
							// first check for reserved tokens
							for (int e=0; e < numVirts; e++)
							{
								for (int f =0; f < bufferDepth; f++)
								{
									if (doneThisVirt == false && ports[ports[a*numPorts + b].next].i_buff[e*bufferDepth+f]%maxMessage==-(ports[a*numPorts + b].o_buff[buff]%maxMessage)) 
									{ // if next input buffer is ready

										// check if header flit, if so, store new port in path
										if (type==0)
										{
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=e;

											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;

										}

										// reserve buffer
										ports[ports[a*numPorts + b].next].i_buff[e*bufferDepth+f] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
										// reserve link
										ports[a*numPorts +b].sent_this_cycle=true;
										// mark for advancing later
										to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
										to_internode_move_oldports[internode_moves]= a*numPorts + b;
										to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
										to_internode_move_virts[internode_moves]=e*bufferDepth+f;
										to_internode_move_oldvirts[internode_moves]=v;

										internode_moves++;
										internode_total++;
										temp_internode_total++;
										if (top_type==CUBE && (dimensions >= 3) && (b==1 || b==2) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==CLUSTERED && (dimensions >= 3) && (b==0 || b==1) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==STACKED && (b== dimensions*2+1)) 
										{
											internode_z++;
										}
										if (top_type==KARY && levels==3) 
										{
											int k=numPorts/2;
											if (a<numIps) 
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) 
												{
													internode_local++;
													temp_internode_local++;
												}
												else 
												{
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+2*numIps/k)) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==BFT && levels==3) 
										{
											int k=numPorts/2+1;
											if (a<numIps) 
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) 
												{
													internode_local++;
													temp_internode_local++;
												}
												else 
												{
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+numIps/k+numIps/(2*k))) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==OCTOM256 || top_type==OCTOM)
										{
											if (b<4)
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (b>3 && b <7)
											{
												internode_mid++;
												temp_internode_mid++;
											}
											else if (b>6)
											{
												internode_long++;
												temp_internode_long++;
											}
										}

										// clear all buffers if it's a tail flit
										if (type == 2)
										{
											for (int x=0; x < bufferDepth; x++)
											{
												if (GHOST) 	ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
												else ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
											}
										}
										else					// leave token behind to save spot for following nodes if not tail
											ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

										e = 1000;	// to exit for loop after successful
										f = 1000;
										doneThisVirt=true;
									}
								} // end for f -> bufferDepth
							} // end for e -> numVirts

							// check for a partially filled virtual channel belonging to this message
							if (doneThisVirt==false)
							{
								for (int m=0; m < numVirts; m++)
								{
									for (int n =0; n < bufferDepth; n++)
									{
										if (ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+n]%maxMessage==(ports[a*numPorts + b].o_buff[buff]%maxMessage)) 
										{ // if next input buffer has the message in it

											emptySpace=-1;
											// check for an empty space in this buffer
											for (int o = 0; o < bufferDepth; o++)
											{
												if (ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+o]==0)
												{
													emptySpace=o;		// save target empty buffer space
													o=1000;	// exit loop
												}
											}

											// if an empty space in the buffer is found, set for advancement
											if (emptySpace!=-1)
											{
												// check if header flit, if so, store new port in path
												if (type==0)
												{
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=m;
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;
												}

												// reserve buffer
												ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+emptySpace] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
												// reserve link
												ports[a*numPorts +b].sent_this_cycle=true;
												// mark for advancing later
												to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
												to_internode_move_oldports[internode_moves]= a*numPorts + b;
												to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
												to_internode_move_virts[internode_moves]=m*bufferDepth+emptySpace;
												to_internode_move_oldvirts[internode_moves]=v;
												internode_moves++;  
												internode_total++;
												temp_internode_total++;
												if (top_type==CUBE && (dimensions >= 3) && (b==1 || b==2) && (a>=numIps)) 
												{
													internode_z++;
												}
												if (top_type==CLUSTERED && (dimensions >= 3) && (b==0 || b==1) && (a>=numIps)) 
												{
													internode_z++;
												}
												if (top_type==STACKED && (b== dimensions*2+1)) 
												{
													internode_z++;
												}
												if (top_type==KARY && levels==3) 
												{
													int k=numPorts/2;
													if (a<numIps) 
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (a < (numIps+numIps/k)) 
													{
														if (b < k) 
														{
															internode_local++;
															temp_internode_local++;
														}
														else 
														{
															internode_mid++;
															temp_internode_mid++;
														}
													}
													else if (a < (numIps+2*numIps/k)) 
													{
														if (b < k) 
														{
															internode_mid++;
															temp_internode_mid++;
														}
														else 
														{
															internode_long++;
															temp_internode_long++;
														}
													}
													else 
													{
														internode_long++;
														temp_internode_long++;
													}
												}
												if (top_type==BFT && levels==3) 
												{
													int k=numPorts/2+1;
													if (a<numIps) 
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (a < (numIps+numIps/k)) 
													{
														if (b < k) 
														{
															internode_local++;
															temp_internode_local++;
														}
														else 
														{
															internode_mid++;
															temp_internode_mid++;
														}
													}
													else if (a < (numIps+numIps/k+numIps/(2*k))) 
													{
														if (b < k) 
														{
															internode_mid++;
															temp_internode_mid++;
														}
														else 
														{
															internode_long++;
															temp_internode_long++;
														}
													}
													else 
													{
														internode_long++;
														temp_internode_long++;
													}
												}
												if (top_type==OCTOM256)
												{
													if (b<4)
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (b>3 && b <7)
													{
														internode_mid++;
														temp_internode_mid++;
													}
													else if (b>6)
													{
														internode_long++;
														temp_internode_long++;
													}
												}

												// clear all buffers if it's a tail flit
												if (type == 2)
												{
													for (int x=0; x < bufferDepth; x++)
													{
														if (GHOST) 	
															ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
														else 
															ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
													}													
												}
												else					// leave token behind to save spot for following nodes if not tail
													ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

												m = 1000;	// to exit for loop after successful
												n = 1000;
												doneThisVirt=true;

											}	// end if empty space != -1
										} 
									} // end for n -> bufferDepth
								} // end for m -> numVirts
							}

							// check for a completely empty virtual channel
							if (doneThisVirt==false && type == 0){ // restricted to headers
								// limit virtual channel use for DOR torus routing
								int start_v = 0;
								int stop_v = numVirts;
								if (top_type==CUBE && WRAP) 
								{
									if (msgs[ports[a*numPorts + b].o_buff[buff]%(maxMessage)].upper==1)
									{
										start_v = numVirts/2;
										stop_v = numVirts;
									}
									else if (msgs[ports[a*numPorts + b].o_buff[buff]%(maxMessage)].upper==0)
									{ 
										start_v = 0;
										stop_v = numVirts/2;
									}
									else 
									{
										cout << "Upper/Lower VC error in set_internode_moves\n";
										cycles=DUR+1;
									}
								}

								for (int h=start_v; h < stop_v; h++)
								{
									allEmpty=true;
									for (int i = 0; i < bufferDepth; i++)
									{
										if (ports[ports[a*numPorts + b].next].i_buff[h*bufferDepth+i]!=0) 
										{ // if next input buffer is empty	
											allEmpty=false;	
										}
									}
									// h is a virt with a totally empty buffer
									if (allEmpty) 
									{ 	
										// check if header flit, if so, store new port in path
										if (type==0)
										{
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=h;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].header_moved=true;
										}

										// reserve buffer 0 of virt h
										ports[ports[a*numPorts + b].next].i_buff[h*bufferDepth] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
										// reserve link
										ports[a*numPorts +b].sent_this_cycle=true;
										// mark for advancing later
										to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
										to_internode_move_oldports[internode_moves]= a*numPorts + b;
										to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
										to_internode_move_virts[internode_moves]=h*bufferDepth;
										to_internode_move_oldvirts[internode_moves]=v;
										msgs[ports[a*numPorts + b].o_buff[buff] % maxMessage].virt=h;
										internode_moves++;
										internode_total++;
										temp_internode_total++;
										if (top_type==CUBE && (dimensions >= 3) && (b==1 || b==2) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==CLUSTERED && (dimensions >= 3) && (b==0 || b==1) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==STACKED && (b== dimensions*2+1)) 
										{
											internode_z++;
										}
										if (top_type==KARY && levels==3) 
										{
											int k=numPorts/2;
											if (a<numIps) {
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) {
													internode_local++;
													temp_internode_local++;
												}
												else {
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+2*numIps/k)) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==BFT && levels==3) 
										{
											int k=numPorts/2+1;
											if (a<numIps) 
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) 
												{
													internode_local++;
													temp_internode_local++;
												}
												else 
												{
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+numIps/k+numIps/(2*k))) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==OCTOM256 || top_type==OCTOM)
										{
											if (b<4)
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (b>3 && b <7)
											{
												internode_mid++;
												temp_internode_mid++;
											}
											else if (b>6)
											{
												internode_long++;
												temp_internode_long++;
											}
										}

										// clear all buffers if it's a tail flit
										if (type == 2)
										{
											for (int x=0; x < bufferDepth; x++)
											{
												if (GHOST) 	ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
												else ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
											}
										}
										else	// leave token behind to save spot for following nodes if not tail
											ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

										h = 1000;	// to exit for loop after successful
										doneThisVirt=true;
									}
								}
							}
						}
						else
						{
							// first check for reserved tokens
							for (int e=0; e < numVirts; e++)
							{
								for (int f =0; f < bufferDepth; f++)
								{
									if (doneThisVirt == false && ports[ports[a*numPorts + b].next].i_buff[e*bufferDepth+f]%maxMessage==-(ports[a*numPorts + b].o_buff[buff]%maxMessage)) 
									{ // if next input buffer is ready

										// check if header flit, if so, store new port in path
										if (type==0)
										{
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=e;
											if(fALASH)
												msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_history[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length] = msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].pathNum;
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;
										}

										// reserve buffer
										ports[ports[a*numPorts + b].next].i_buff[e*bufferDepth+f] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
										// reserve link
										ports[a*numPorts +b].sent_this_cycle=true;
										// mark for advancing later
										to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
										to_internode_move_oldports[internode_moves]= a*numPorts + b;
										to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
										to_internode_move_virts[internode_moves]=e*bufferDepth+f;
										to_internode_move_oldvirts[internode_moves]=v;

										internode_moves++;
										internode_total++;
										temp_internode_total++;
										if (top_type==CUBE && (dimensions >= 3) && (b==1 || b==2) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==CLUSTERED && (dimensions >= 3) && (b==0 || b==1) && (a>=numIps)) 
										{
											internode_z++;
										}
										if (top_type==STACKED && (b== dimensions*2+1)) 
										{
											internode_z++;
										}
										if (top_type==KARY && levels==3) 
										{
											int k=numPorts/2;
											if (a<numIps) 
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) 
												{
													internode_local++;
													temp_internode_local++;
												}
												else 
												{
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+2*numIps/k)) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==BFT && levels==3) 
										{
											int k=numPorts/2+1;
											if (a<numIps) 
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (a < (numIps+numIps/k)) 
											{
												if (b < k) 
												{
													internode_local++;
													temp_internode_local++;
												}
												else 
												{
													internode_mid++;
													temp_internode_mid++;
												}
											}
											else if (a < (numIps+numIps/k+numIps/(2*k))) 
											{
												if (b < k) 
												{
													internode_mid++;
													temp_internode_mid++;
												}
												else 
												{
													internode_long++;
													temp_internode_long++;
												}
											}
											else 
											{
												internode_long++;
												temp_internode_long++;
											}
										}
										if (top_type==OCTOM256 || top_type==OCTOM)
										{
											if (b<4)
											{
												internode_local++;
												temp_internode_local++;
											}
											else if (b>3 && b <7)
											{
												internode_mid++;
												temp_internode_mid++;
											}
											else if (b>6)
											{
												internode_long++;
												temp_internode_long++;
											}
										}

										// clear all buffers if it's a tail flit
										if (type == 2)
										{
											for (int x=0; x < bufferDepth; x++)
											{
												if (GHOST) 	ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
												else ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
											}
										}
										else					// leave token behind to save spot for following nodes if not tail
											ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

										e = 1000;	// to exit for loop after successful
										f = 1000;
										doneThisVirt=true;
									}
								} // end for f -> bufferDepth
							} // end for e -> numVirts

							// check for a partially filled virtual channel belonging to this message
							if (doneThisVirt==false)
							{
								for (int m=0; m < numVirts; m++)
								{
									for (int n =0; n < bufferDepth; n++)
									{
										if (ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+n]%maxMessage==(ports[a*numPorts + b].o_buff[buff]%maxMessage)) 
										{ // if next input buffer has the message in it

											emptySpace=-1;
											// check for an empty space in this buffer
											for (int o = 0; o < bufferDepth; o++)
											{
												if (ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+o]==0)
												{
													emptySpace=o;		// save target empty buffer space
													o=1000;	// exit loop
												}
											}

											// if an empty space in the buffer is found, set for advancement
											if (emptySpace!=-1)
											{
												// check if header flit, if so, store new port in path
												if (type==0)
												{
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=m;
													if(fALASH)
														msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_history[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length] = msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].pathNum;
													msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;
												}

												// reserve buffer
												ports[ports[a*numPorts + b].next].i_buff[m*bufferDepth+emptySpace] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
												// reserve link
												ports[a*numPorts +b].sent_this_cycle=true;
												// mark for advancing later
												to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
												to_internode_move_oldports[internode_moves]= a*numPorts + b;
												to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
												to_internode_move_virts[internode_moves]=m*bufferDepth+emptySpace;
												to_internode_move_oldvirts[internode_moves]=v;
												internode_moves++;  
												internode_total++;
												temp_internode_total++;
												if (top_type==CUBE && (dimensions >= 3) && (b==1 || b==2) && (a>=numIps)) 
												{
													internode_z++;
												}
												if (top_type==CLUSTERED && (dimensions >= 3) && (b==0 || b==1) && (a>=numIps)) 
												{
													internode_z++;
												}
												if (top_type==STACKED && (b== dimensions*2+1)) 
												{
													internode_z++;
												}
												if (top_type==KARY && levels==3) 
												{
													int k=numPorts/2;
													if (a<numIps) 
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (a < (numIps+numIps/k)) 
													{
														if (b < k) 
														{
															internode_local++;
															temp_internode_local++;
														}
														else 
														{
															internode_mid++;
															temp_internode_mid++;
														}
													}
													else if (a < (numIps+2*numIps/k)) 
													{
														if (b < k) 
														{
															internode_mid++;
															temp_internode_mid++;
														}
														else 
														{
															internode_long++;
															temp_internode_long++;
														}
													}
													else 
													{
														internode_long++;
														temp_internode_long++;
													}
												}
												if (top_type==BFT && levels==3) 
												{
													int k=numPorts/2+1;
													if (a<numIps) 
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (a < (numIps+numIps/k)) 
													{
														if (b < k) 
														{
															internode_local++;
															temp_internode_local++;
														}
														else 
														{
															internode_mid++;
															temp_internode_mid++;
														}
													}
													else if (a < (numIps+numIps/k+numIps/(2*k))) 
													{
														if (b < k) 
														{
															internode_mid++;
															temp_internode_mid++;
														}
														else 
														{
															internode_long++;
															temp_internode_long++;
														}
													}
													else 
													{
														internode_long++;
														temp_internode_long++;
													}
												}
												if (top_type==OCTOM256)
												{
													if (b<4)
													{
														internode_local++;
														temp_internode_local++;
													}
													else if (b>3 && b <7)
													{
														internode_mid++;
														temp_internode_mid++;
													}
													else if (b>6)
													{
														internode_long++;
														temp_internode_long++;
													}
												}

												// clear all buffers if it's a tail flit
												if (type == 2)
												{
													for (int x=0; x < bufferDepth; x++)
													{
														if (GHOST) 	
															ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
														else 
															ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
													}													
												}
												else					// leave token behind to save spot for following nodes if not tail
													ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

												m = 1000;	// to exit for loop after successful
												n = 1000;
												doneThisVirt=true;

											}	// end if empty space != -1
										} 
									} // end for n -> bufferDepth
								} // end for m -> numVirts
							}

							// check for a completely empty virtual channel
							if (doneThisVirt==false && type == 0){ // restricted to headers
								// limit virtual channel use for DOR torus routing

								int h;
								int layer_checked[4] = {0,0,0,0};
								if(msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].path_length !=1)
									h = msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].vpath[msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].path_length-1];
								else
									h = msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].layer;
								
								if(fALASH)
								{
									if(msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].path_length ==1)
									{
										double best_commDens = -1;
										double commDens = 0;
										int bestLayer = -1;
										int startNode = msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].source[0];
										int destNode = msgs[ports[a*numPorts + b].o_buff[buff]%maxMessage].dest[0];

										for(int i = 0; i < numVirts; i++)
										{
											layer_checked[i] = 0;
										}
										for(int l = 0; l < numLayers; l++)
										{
											bestLayer = -1;
											best_commDens = -1;
											for(int j = 0; j < numLayers; j++)
											{
												if(layer_checked[j] == 0)
												{
													for(int i = 0; i < maxPaths; i++)
													{
														commDens = 0;
														if(pathAllocLayer[startNode][destNode][i][j] == 1)
														{
															for(int k =1; k < MultiPathLength[startNode][destNode][i]-2; k++)
															{
																commDens += communication_density[MultiPathMsg[startNode][destNode][i][k]][MultiPathMsg[startNode][destNode][i][k+1]][j];
															}
															if(commDens < best_commDens || best_commDens == -1)
															{
																best_commDens = commDens;
																bestLayer = j;
															}
														}
													}
												}
											}
											if(bestLayer != -1)
											{
												allEmpty=true;
												h = bestLayer;
												layer_checked[bestLayer] = 1;
												for (int i = 0; i < bufferDepth; i++)
												{
													if (ports[ports[a*numPorts + b].next].i_buff[h*bufferDepth+i]!=0) 
													{ // if next input buffer is empty	
														allEmpty=false;	
													}
												}
												if(allEmpty)
													break;
											}
										}
									}
								}

								allEmpty=true;
								for (int i = 0; i < bufferDepth; i++)
								{
									if (ports[ports[a*numPorts + b].next].i_buff[h*bufferDepth+i]!=0) 
									{ // if next input buffer is empty	
										allEmpty=false;	
									}
								}

								// h is a virt with a totally empty buffer
								if (allEmpty) 
								{ 	
									// check if header flit, if so, store new port in path
									if (type==0)
									{
										if(fALASH)
											msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_history[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length] = msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].pathNum;
										msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=ports[a*numPorts + b].next;
										msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length]=h;
										msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].path_length++;
										msgs[ports[a*numPorts + b].o_buff[buff] % (2*maxMessage)].header_moved=true;
									}

									// reserve buffer 0 of virt h
									ports[ports[a*numPorts + b].next].i_buff[h*bufferDepth] = -(ports[a*numPorts + b].o_buff[buff]%maxMessage);
									// reserve link
									ports[a*numPorts +b].sent_this_cycle=true;
									// mark for advancing later
									to_internode_move_ports[internode_moves]=ports[a*numPorts + b].next;
									to_internode_move_oldports[internode_moves]= a*numPorts + b;
									to_internode_move_flits[internode_moves]=ports[a*numPorts + b].o_buff[buff];
									to_internode_move_virts[internode_moves]=h*bufferDepth;
									to_internode_move_oldvirts[internode_moves]=v;
									msgs[ports[a*numPorts + b].o_buff[buff] % maxMessage].virt=h;
									internode_moves++;
									internode_total++;
									temp_internode_total++;

									// clear all buffers if it's a tail flit
									if (type == 2)
									{
										for (int x=0; x < bufferDepth; x++)
										{
											if (GHOST) 	ports[a*numPorts + b].o_buff[v*bufferDepth+x] = RES_TOKEN1;
											else ports[a*numPorts + b].o_buff[v*bufferDepth+x] = 0;
										}
									}
									else	// leave token behind to save spot for following nodes if not tail
										ports[a*numPorts + b].o_buff[buff] = -(ports[a*numPorts + b].o_buff[buff] % maxMessage);	

									h = 1000;	// to exit for loop after successful
									doneThisVirt=true;
								}

							} 
						}

					}	// type != -1
				} // end if not send this cycle
			} // end for virts c
		}  // end for ports
	} // end for nodes nodes
}  // end set_internode_moves
// scan through all input ports

void set_intranode_moves(int start_node, int stop_node, int start_port, int stop_port) {
	int port;
	int b = 0;
	int level=0;
	int emptySpace=-1;
	bool allEmpty=false;
	bool doneThisVirt = false;
	int v=-1;  // current virt being served
	bool ok; 
	bool gateway = false; // for octo5
	int type;
	int buff;
	int ring = -1;	// current ring for octo5 topology
	int ring_of_8, ring_of_64; // currnet rings for octom3
	int node_limit;



	if (top_type==OCTO5) 
		node_limit=numNodes+3;	// to scan extra ports of gateways
	else 
		node_limit = numNodes;


	for (int a = start_node; a <= stop_node; a++) 
	{

		if (top_type==BFT) 
			level=find_level_bft(a);
		else if (top_type==KARY) 
			level=find_level_kary(a);

		for (int z = start_port; z <= stop_port; z++) 
		{
			//b = (z+find_oldest(a,start_port,stop_port))%(stop_port-start_port+1) + start_port;  // fix this
			b=z;	

			// find oldest message in i_buffs and start there


			for (int d=0; d < numVirts; d++)
			{
				if (ports[a*numPorts +b].sent_this_cycle_intra!=true)
				{
					ok = true;
					doneThisVirt=false;

					// find buffer here
					type = -1;
					v = (ports[a*numPorts +b].last_virt_sent_intra+1+d)%numVirts;

					// search for header flits, then data, then tail to keep order
					for (int w = 0; w < bufferDepth; w++)
					{
						if (ports[a*numPorts + b].i_buff[v*bufferDepth+w] >2*maxMessage)
						{	// header flit found
							type = 0;
							type = -2;	// skip headers
							buff = v*bufferDepth+w;
							w = bufferDepth +10;  // to exit loop
						}
					}
					if (type==-1)
					{
						for (int z = 0; z < bufferDepth; z++){
							if (ports[a*numPorts + b].i_buff[v*bufferDepth+z]>0 && ports[a*numPorts + b].i_buff[v*bufferDepth+z]<maxMessage){	// data flit found
								type = 1;	// data
								buff = v*bufferDepth+z;
								z = bufferDepth +10;  // to exit loop
							}
						}
					}
					if (type==-1){
						for (int y = 0; y < bufferDepth; y++){
							if (ports[a*numPorts + b].i_buff[v*bufferDepth+y]>maxMessage){	// tail flit found
								type = 2; // tail
								buff = v*bufferDepth+y;
								y = bufferDepth +10;  // to exit loop
							}
						}
					}
					if(type > 0)
					{
						if(msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].wait != -1)
						{
							if(type == 1 && (a*numPorts+b) == msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].path[msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].path_length-2])
							{
								type = -1;
							}
						}
					}


					// there is a flit to send, look for a destination buffer
					if (type != -1 && doneThisVirt == false) { 
						if (type==0){  // if it's a header flit
							if (top_type==BFT || top_type==KARY)
							{
								port = tree_route(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));								
							}

							/*if (top_type==RING){
							port = ring_route(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));
							}*/
							/*if (top_type==MESH){
							port = mesh_route(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));									
							}*/
							if (top_type==SUPERS)
							{
								port = ss_route_rand(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));
							}

							if (top_type==CUBE){
								if (!WRAP)
									port = cube_route_mesh(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));								
								else
									port = cube_route_torus(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));								
							}
							if (top_type==CLUSTERED){
								if (!WRAP)
									port = clustered_route_mesh(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));								
								else
									port = clustered_route_torus(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));								
							}
							if (top_type==STACKED){
								if (!WRAP)
									port = stacked_route_mesh(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));
								else
									port = stacked_route_torus(ports[a*numPorts + b].i_buff[buff] % (2*maxMessage));
							}

							if (top_type==OCTO){
								// if destination reached
								if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
									port= a*numPorts;
								// if straight across
								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-numIps+4)%numIps)
									port = a*numPorts+3;	
								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-numIps+1)%numIps ||
									msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-numIps+2)%numIps ||
									msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-3)%numIps)
									port= a*numPorts +2;	// go up in number
								else
									port = a*numPorts +1;	// go down in number
								if (octoTraffic==1){	// avoid using 0-7, 7-0 links
									if (a==7 && port==a*numPorts+2) 
										port = a*numPorts+1;	// go down to 6 instead
									if (a==6 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==0) 
										port = a*numPorts+1;	// go down to 5 instead
									if (a==0 && port==a*numPorts+1) 
										port = a*numPorts+2;	// go up to 1 instead
									if (a==1 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==7) 
										port = a*numPorts+2;	// go up to 2 instead
								}
							}

							if (top_type==OCTOM3){
								ring_of_8 = (int) (a-numIps)/8;
								ring_of_64 = (int) (a-numIps)/64;

								// if destination is in local ring
								if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == ring_of_8){
									if (octoTraffic==0){
										// if destination reached
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
											port= a*numPorts;
										// if straight across
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+4)%8 + ring_of_8*8)
											port = a*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+1)%8 + ring_of_8*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+2)%8  + ring_of_8*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-3)%8  + ring_of_8*8)
											port= a*numPorts +2;	// go up in number
										else
											port = a*numPorts +1;	// go down in number
									}
									else {
										// if destination reached
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
											port= a*numPorts;
										// if straight across
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+4)%8 + ring_of_8*8)
											port = a*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+1)%8 + ring_of_8*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+2)%8  + ring_of_8*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-3)%8  + ring_of_8*8)
											port= a*numPorts +2;	// go up in number
										else
											port = a*numPorts +1;	// go down in number



									}
								}
								// need to move to appropriate ring_of_8, it's in the right 64 IP ring
								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == ring_of_64) {
									if (octoTraffic==0){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+1)%8 + ring_of_64*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+2)%8 + ring_of_64*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+5)%8 + ring_of_64*8)
											port = a*numPorts + 5;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+4)%8 + ring_of_64*8)
											port = a*numPorts + 6;
										else 
											port = a*numPorts + 4;
									}
									else {
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+1)%8 + ring_of_64*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+2)%8 + ring_of_64*8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+5)%8 + ring_of_64*8)
											port = a*numPorts + 5;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+4)%8 + ring_of_64*8)
											port = a*numPorts + 6;
										else 
											port = a*numPorts + 4;
										// correct to eliminate cycles
										if (ring_of_8==7 && port == a*numPorts+5)
											port = a*numPorts+4;
										if (ring_of_8==6 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] ==0)
											port = a*numPorts+4;
										if (ring_of_8==0 && port == a*numPorts+4)
											port = a*numPorts+5;
										if (ring_of_8==1 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] ==7)
											port = a*numPorts+5;

									}
								}
								// need to move to appropriate ring_of_64
								else {
									if (octoTraffic==0){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+1)%8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+2)%8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+5)%8)
											port = a*numPorts + 8;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+4)%8)
											port = a*numPorts + 9;
										else 
											port = a*numPorts + 7;
									}
									else {
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+1)%8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+2)%8 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+5)%8)
											port = a*numPorts + 8;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+4)%8)
											port = a*numPorts + 9;
										else 
											port = a*numPorts + 7;
										// correct to eliminate cycles
										if (ring_of_64==7 && port == a*numPorts+8)
											port = a*numPorts+7;
										if (ring_of_64==6 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] ==0)
											port = a*numPorts+7;
										if (ring_of_64==0 && port == a*numPorts+7)
											port = a*numPorts+8;
										if (ring_of_64==1 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] ==7)
											port = a*numPorts+8;
									}
								}
							}
							if (top_type==OCTOM256){
								ring_of_8 = (int) (a-numIps)/8;
								ring_of_64 = (int) (a-numIps)/64;

								// if destination is in local ring
								if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == ring_of_8){
									// if destination reached
									if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
										port= a*numPorts;
									// if straight across
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+4)%8 + ring_of_8*8)
										port = a*numPorts+3;	
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+1)%8 + ring_of_8*8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a+2)%8  + ring_of_8*8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == (a-3)%8  + ring_of_8*8)
										port= a*numPorts +2;	// go up in number
									else
										port = a*numPorts +1;	// go down in number
								}
								// need to move to appropriate ring_of_8, it's in the right 64 IP ring
								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == ring_of_64) {
									if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+1)%8 + ring_of_64*8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+2)%8 + ring_of_64*8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+5)%8 + ring_of_64*8)
										port = a*numPorts + 5;
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] == (ring_of_8+4)%8 + ring_of_64*8)
										port = a*numPorts + 6;
									else 
										port = a*numPorts + 4;
									if (octoTraffic!=0){
										// correct to eliminate cycles
										if (ring_of_8==7 && port == a*numPorts+5)
											port = a*numPorts+4;
										if (ring_of_8==6 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] ==0)
											port = a*numPorts+4;
										if (ring_of_8==0 && port == a*numPorts+4)
											port = a*numPorts+5;
										if (ring_of_8==1 && msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1] ==7)
											port = a*numPorts+5;
									}
								}
								// need to move to appropriate ring_of_64
								else {
									if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+1)%4)
										port = a*numPorts + 8;
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[2] == (ring_of_64+2)%4)
										port = a*numPorts + 9;
									else 
										port = a*numPorts + 7;
									if (octoTraffic!=0){
										// correct to eliminate cycles
										if (ring_of_64==3 && port == a*numPorts+8)
											port = a*numPorts+7;
										if (ring_of_64==0 && port == a*numPorts+7)
											port = a*numPorts+8;
									}
								}
							}


							if (top_type==OCTO5){
								ring = (int) (a-36)/8;
								gateway=false;
								if (a==36 || a==44 || a==52 || a==60 || a>=numNodes) gateway=true;

								// if centre ring, do special cases

								if (ring==4 && !gateway){
									// if destination is in centre ring, 
									if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==4){
										// if dest reached
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
											port= a*numPorts;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps+2)%4)
											port = a*numPorts+3;
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps+1)%4)											
											port= a*numPorts +2;	// go up in number
										else
											port = a*numPorts +1;	// go down in number
									}
									else {
										if (a==68){
											if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==0 ||
												msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==2)
												port = a*numPorts+1;
											else 
												port = a*numPorts+2;
										}
										else if (a==69){
											if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==1 ||
												msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==3)
												port = a*numPorts+1;
											else 
												port = a*numPorts+2;
										}
										else if (a==70){
											if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==2 ||
												msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==0)
												port = a*numPorts+1;
											else 
												port = a*numPorts+2;
										}
										else if (a==71){
											if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==1 ||
												msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==3)
												port = a*numPorts+1;
											else 
												port = a*numPorts+2;
										}
									}
								}
								else if (gateway){
									if (a==36 || a*numPorts+b==288 || a*numPorts+b==289 || a*numPorts+b==296){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==3 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==35 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==33 )
											port = 288; // to node 71
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==1 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==32 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==34 )
											port = 289; // to node 68
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==2)
											port = 296;	// to node 52
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 4)
											port = 36*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 1 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 2 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 5)
											port= 36*numPorts +2;	// go up in number
										else
											port = 36*numPorts +1;	// go down in number
									}
									else if (a==44 || a*numPorts+b==290 || a*numPorts+b==291 || a*numPorts+b==297){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==0 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==32 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==34 )
											port = 290; // to node 68
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==2 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==33 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==35 )
											port = 291; // to node 69
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==3)
											port = 297;	// to node 60
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 12)
											port = 44*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 9 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 10 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 13)
											port= 44*numPorts +2;	// go up in number
										else
											port = 44*numPorts +1;	// go down in number
									}
									else if (a==52 || a*numPorts+b==292 || a*numPorts+b==293 || a*numPorts+b==298){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==1 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==33 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==35 )
											port = 292; // to node 69
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==3 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==32 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==34 )
											port = 293; // to node 70
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==0)
											port = 298;	// to node 36
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 20)
											port = 52*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 17 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 18 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 21)
											port= 52*numPorts +2;	// go up in number
										else
											port = 52*numPorts +1;	// go down in number
									}
									else if (a==60 || a*numPorts+b==294 || a*numPorts+b==295 || a*numPorts+b==299){
										if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==2 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==34 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==32 )
											port = 294; // to node 70
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==0 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==33 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0]==35 )
											port = 295; // to node 71
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==1)
											port = 299;	// to node 44
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 28)
											port = 60*numPorts+3;	
										else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 25 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 26 ||
											msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == 29)
											port= 60*numPorts +2;	// go up in number
										else
											port = 60*numPorts +1;	// go down in number
									}

								}

								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]!=ring && !gateway){
									// route towards 0 position of current ring
									if (0 == (a-numIps+4)%8)
										port = a*numPorts+3;
									else if (0 == (a-numIps+1)%8 || 0==(a-numIps+2)%8 || 0==(a-numIps-3)%8)
										port= a*numPorts +2;	// go up in number
									else 
										port = a*numPorts +1;

								}
								else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[1]==ring && !gateway){
									// else if dest is in same ring, pass along like old times
									// if destination reached
									if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == a-numIps)
										port= a*numPorts;
									// if straight across
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps+4)%8)
										port = a*numPorts+3;	
									else if (msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps+1)%8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps+2)%8 ||
										msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].dest[0] == ring*8+(a-numIps-3)%8)
										port= a*numPorts +2;	// go up in number
									else
										port = a*numPorts +1;	// go down in number
								}
							}
							// ************************ now find an open virtual channal **************************************************						
							// check if o_buff of that port is completely empty, and set flit for advancing
							// restrict available virts in the case of torus.
							int start_v = 0;
							int stop_v = numVirts;
							if (top_type==CUBE && WRAP) {
								if (msgs[ports[a*numPorts + b].i_buff[buff]%(maxMessage)].upper==1){
									start_v = numVirts/2;
									stop_v = numVirts;
								}
								else if (msgs[ports[a*numPorts + b].i_buff[buff]%(maxMessage)].upper==0){ 
									start_v = 0;
									stop_v = numVirts/2;
								}
								else {
									cout << "Upper/Lower VC error\n";
									cycles=DUR+1;
								}
							}
							for (int e =start_v; e < stop_v; e++){
								allEmpty=true;
								for (int x =0; x < bufferDepth; x ++){
									if (ports[port].o_buff[e*bufferDepth+x]!=0){
										allEmpty=false;
										x = bufferDepth+10;
									}
								}

								// this lane is totally free for the taking.
								if (allEmpty) {
									ports[port].o_buff[e*bufferDepth]=-(ports[a*numPorts + b].i_buff[buff] % maxMessage);		// this marker reserves the first space in the o_buff until the intranode moves are processed
									to_intranode_move_ports[intranode_moves]=port;
									to_intranode_move_oldports[intranode_moves]=a*numPorts +b;
									to_intranode_move_flits[intranode_moves]=ports[a*numPorts + b].i_buff[buff];
									to_intranode_move_virts[intranode_moves]=e*bufferDepth;
									to_intranode_move_oldvirts[intranode_moves]=v;
									intranode_moves++;
									if (type==0){
										intranode_header_total++;
										temp_intranode_header_total++;
									}
									else if (type>0){
										intranode_data_total++;
										temp_intranode_data_total++;
									}
									doneThisVirt=true;
									ports[a*numPorts +b].sent_this_cycle_intra=true;
									// update message path
									msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].path[msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].path_length]=port;
									msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].vpath[msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].path_length]=e;
									msgs[ports[a*numPorts + b].i_buff[buff] % (2*maxMessage)].path_length++;

									ports[a*numPorts + b].i_buff[buff] = -(ports[a*numPorts + b].i_buff[buff]%maxMessage);	// leave marker to reserve buffer for rest of message
									e = 10000;  // set e to exit for loop after success
								}
							} // end for e-> numVirts	
						}	// end if header
					}



					if (type>0 && doneThisVirt==false){  // it's not a header so we must search through msg path to find next port
						for (int c = 1; c < msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].path_length; c=c+2){
							if (msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].path[c]==(a*numPorts+b)) {    // if current port is found in path
								port = msgs[ports[a*numPorts + b].i_buff[buff]%maxMessage].path[c+1];	// set port to next one
								c=100000;  // exit the for loop
							}	
						}	
						// check for tokens, then partially filled, then completely empty


						if (doneThisVirt==false){
							// set flit for advancing if possible
							for (int f = 0; f < numVirts; f++){
								for (int x=0; x < bufferDepth; x++){
									if ((ports[port].o_buff[f*bufferDepth+x]==-(ports[a*numPorts + b].i_buff[buff]%maxMessage))){
										ports[port].o_buff[f*bufferDepth+x]=-(ports[a*numPorts + b].i_buff[buff] % maxMessage);;		// this marker reserves the o_buff until the intranode moves are processed
										to_intranode_move_ports[intranode_moves]=port;
										to_intranode_move_flits[intranode_moves]=ports[a*numPorts + b].i_buff[buff];
										to_intranode_move_virts[intranode_moves]=f*bufferDepth+x;
										to_intranode_move_oldvirts[intranode_moves]=v;
										to_intranode_move_oldports[intranode_moves]=a*numPorts +b;
										intranode_moves++;
										if (type==0) {
											temp_intranode_header_total++;
											intranode_header_total++;											
										}
										else if (type>0) {
											temp_intranode_data_total++;
											intranode_data_total++;
										}
										doneThisVirt=true;
										ports[a*numPorts +b].sent_this_cycle_intra=true;

										// clear buffer if it's a tail flit
										if (type==2)
											for (int x = 0; x < bufferDepth; x++){
												if (GHOST) 	ports[a*numPorts + b].i_buff[v*bufferDepth+x] = RES_TOKEN1;
												else ports[a*numPorts + b].i_buff[v*bufferDepth+x] = 0;
											}
										else 	// leave token behind to save spot for following nodes if not tail
											ports[a*numPorts + b].i_buff[buff] = -(ports[a*numPorts + b].i_buff[buff] % maxMessage);
										f = 10000; // set f to exit for loop
										x = 10000;

									}
								}
							}
						}
						if (doneThisVirt==false){
							// look for partially filled buffers
							for (int g=0; g < numVirts; g++){
								for (int x=0; x < bufferDepth; x++){
									if (ports[port].o_buff[g*bufferDepth+x]==ports[a*numPorts + b].i_buff[buff]%maxMessage) { // if next input buffer has the message in it

										emptySpace=-1;
										// check for an empty space in this buffer
										for (int o = 0; o < bufferDepth; o++){
											if (ports[port].o_buff[g*bufferDepth+o]==0){
												emptySpace=o;		// save target empty buffer space
												o=1000;	// exit loop
											}
										}

										// if an empty space in the buffer is found, set for advancement
										if (emptySpace!=-1){
											ports[port].o_buff[g*bufferDepth+emptySpace]=-(maxMessage+1);		// this marker reserves the o_buff until the intranode moves are processed
											to_intranode_move_ports[intranode_moves]=port;
											to_intranode_move_flits[intranode_moves]=ports[a*numPorts + b].i_buff[buff];
											to_intranode_move_virts[intranode_moves]=g*bufferDepth+emptySpace;
											to_intranode_move_oldvirts[intranode_moves]=v;
											to_intranode_move_oldports[intranode_moves]=a*numPorts +b;
											intranode_moves++;
											if (type==0) {
												intranode_header_total++;
												temp_intranode_header_total++;
											}
											else if (type>0) {
												intranode_data_total++;
												temp_intranode_data_total++;
											}
											doneThisVirt=true;
											ports[a*numPorts +b].sent_this_cycle_intra=true;

											// clear buffer if it's a tail flit
											if (type==2)
												for (int x = 0; x < bufferDepth; x++){
													if (GHOST) 	ports[a*numPorts + b].i_buff[v*bufferDepth+x] = RES_TOKEN1;
													else ports[a*numPorts + b].i_buff[v*bufferDepth+x] = 0;
												}
											else		// leave token behind to save spot for following nodes if not tail
												ports[a*numPorts + b].i_buff[buff] = -(ports[a*numPorts + b].i_buff[buff] % maxMessage);
											g = 10000; // set f to exit for loop
											x = 10000;
										}
									}
								} // end x-> bufferDepth
							} // end g-> numVirts
						}	// done this virt

						// look for completely empty buffer
						if (doneThisVirt==false && type ==0){	// restricted to headers, this never happens.
							cout << "We actaully get here\n";
							for (int g = 0; g < numVirts; g++){
								allEmpty=true;
								for (int i = 0; i < bufferDepth; i++){
									if (ports[port].o_buff[g*bufferDepth+i]!=0) { // if next input buffer is empty	
										allEmpty=false;	
									}
								}
								// h is a virt with a totally empty buffer
								if (allEmpty) { 
									ports[port].o_buff[g*bufferDepth]=-(maxMessage+1);		// this marker reserves the o_buff until the intranode moves are processed
									to_intranode_move_ports[intranode_moves]=port;
									to_intranode_move_flits[intranode_moves]=ports[a*numPorts + b].i_buff[buff];
									to_intranode_move_virts[intranode_moves]=g*bufferDepth;
									to_intranode_move_oldvirts[intranode_moves]=v;
									to_intranode_move_oldports[intranode_moves]=a*numPorts +b;
									intranode_moves++;
									if (type==0) {
										intranode_header_total++;
										temp_intranode_header_total++;
									}
									else if (type>0) {
										intranode_data_total++;
										temp_intranode_data_total++;
									}
									doneThisVirt=true;
									ports[a*numPorts +b].sent_this_cycle_intra=true;

									// clear buffer if it's a tail flit
									if (type==2)
										for (int x = 0; x < bufferDepth; x++){
											if (GHOST) 	ports[a*numPorts + b].i_buff[v*bufferDepth+x] = RES_TOKEN1;
											else ports[a*numPorts + b].i_buff[v*bufferDepth+x] = 0;
										}
									else		// leave token behind to save spot for following nodes if not tail
										ports[a*numPorts + b].i_buff[buff] = -(ports[a*numPorts + b].i_buff[buff] % maxMessage);
									g = 10000; // set f to exit for loop
								} // end all empty
							}  // end g -> numVirts
						}
					} // end not header
				} // end if not sent this cycle intra
			} // end for d-> numVirts
		}	//end for z-> numPorts
	}	// end for a-> numNodes
}

// go through messages and label those blocked.  
// used in priority collision handling
void detect_blocking(){
	int m = firstMsg;

	for (int a =0; a < numActiveMsgs; a++){
		if (!msgs[m].header_moved && !msgs[m].header_done) {
			msgs[m].is_blocked=true;
		}
		else msgs[m].is_blocked=false;

		// advance to next message
		if (msgs[m].next<1 && a!=numActiveMsgs-1) cout << "ERROR in detect collions\n";
		else m = msgs[m].next;
	}
	m = firstMsg;
	for (int a =0; a < numActiveMsgs; a++){
		if (msgs[m].is_blocked) {
			// look through requested port for blocked messages
			for (int b=0; b < numVirts*bufferDepth; b++)
			{
				if (msgs[m].header_in) 
				{
					if (ports[msgs[m].req_port].o_buff[b]!=0)
					{
						// for data, tail and header flits
						if (ports[msgs[m].req_port].o_buff[b]>0)
						{
							if (msgs[ports[msgs[m].req_port].o_buff[b]%maxMessage].is_blocked
								&& max(msgs[ports[msgs[m].req_port].o_buff[b]%maxMessage].priority,msgs[ports[msgs[m].req_port].o_buff[b]%maxMessage].temp_priority) < max(msgs[m].priority,msgs[m].temp_priority))
							{
								// inherit priority
								msgs[ports[msgs[m].req_port].o_buff[b]%maxMessage].temp_priority = max(msgs[m].priority,msgs[m].temp_priority);
								b=numVirts*bufferDepth;		// only do one inheritance
							}
						}
						// for reserved tokens
						else if (ports[msgs[m].req_port].o_buff[b]<0)
						{
							if (msgs[-ports[msgs[m].req_port].o_buff[b]].is_blocked
								&& max(msgs[-ports[msgs[m].req_port].o_buff[b]].priority,msgs[-ports[msgs[m].req_port].o_buff[b]].temp_priority) < max(msgs[m].priority,msgs[m].temp_priority))
							{
								// inherit priority
								msgs[-ports[msgs[m].req_port].o_buff[b]].temp_priority = max(msgs[m].priority,msgs[m].temp_priority);
								b=numVirts*bufferDepth;		// only do one inheritance
							}
						}
					}
				}
				// now the case for headers in out ports
				else if (!msgs[m].header_in){
					// reqested port is the one at the other end of the link
					msgs[m].req_port=ports[msgs[m].path[msgs[m].path_length-1]].next;
					if (ports[msgs[m].req_port].i_buff[b]!=0){
						// for data, tail and header flits
						if (ports[msgs[m].req_port].i_buff[b]>0){
							if (msgs[ports[msgs[m].req_port].i_buff[b]%maxMessage].is_blocked
								&& max(msgs[ports[msgs[m].req_port].i_buff[b]%maxMessage].priority,msgs[ports[msgs[m].req_port].i_buff[b]%maxMessage].temp_priority) < max(msgs[m].priority,msgs[m].temp_priority)){
									// inherit priority
									msgs[ports[msgs[m].req_port].i_buff[b]%maxMessage].temp_priority = max(msgs[m].priority,msgs[m].temp_priority);
									b=numVirts*bufferDepth;		// only do one inheritance
							}
						}
						// for reserved tokens
						else if (ports[msgs[m].req_port].i_buff[b]<0){
							if (msgs[-ports[msgs[m].req_port].i_buff[b]].is_blocked
								&& max(msgs[-ports[msgs[m].req_port].i_buff[b]].priority,msgs[-ports[msgs[m].req_port].i_buff[b]].temp_priority) < max(msgs[m].priority,msgs[m].temp_priority)){
									// inherit priority
									msgs[-ports[msgs[m].req_port].i_buff[b]].temp_priority = max(msgs[m].priority,msgs[m].temp_priority);
									b=numVirts*bufferDepth;		// only do one inheritance
							}
						}
					}
				}
			}		// end for b-> numVirts*bufferDepth
		}

		// advance to next message
		if (msgs[m].next<1 && a!=numActiveMsgs-1) cout << "ERROR in detect collions\n";
		else m = msgs[m].next;
	}
}




// detect collisions in nodes by searching for headers and blocked messages
void detect_collisions(){	
	// go through active messages, and route towards port
	int i;
	int m = firstMsg;	// used to advance through list
	int port;
	int oldest_msg;	// for determining order when using oldest goes first
	int oldest_time, highest_priority, highest_priority_msg;
	int waiting=0;
	bool ok=false;  // for torus VC splitting.
	for (int x =0; x < total_num_of_ports; x++){
		headers[x].numRequested=0;
		headers[x].firstCollision=-1;
		headers[x].currentCollision=-1;
	}

	for (int a = 0; a < numActiveMsgs; a++){
		msgs[m].next_collide=-1;
		if (!msgs[m].header_moved && !msgs[m].header_done && msgs[m].header_in && msgs[m].wait == -1) {
			if (top_type==BFT || top_type==KARY)
				port = tree_route(m);								
			if (top_type==CUBE){
				if (!WRAP)
					port = cube_route_mesh(m);								
				else
					port = cube_route_torus(m);								
			}
			if (top_type==SUPERS)
			{
				port = ss_route_rand(m);
			}
			if (top_type==CLUSTERED){
				if (!WRAP)
					port = clustered_route_mesh(m);								
				else
					port = clustered_route_torus(m);								
			}
			if (top_type==STACKED){
				if (!WRAP)
					port = stacked_route_mesh(m);
				else
					port = stacked_route_torus(m);
			}

			else if (top_type==OCTOM)
				port = route_octom(m);
			else if (top_type==OCTOM256)
				port = route_octom256(m);
			if(port != -1)
			{
				msgs[m].req_port=port;
				// add to headers array
				headers[port].numRequested++;
				if (headers[port].firstCollision==-1) {
					headers[port].firstCollision=m;
					headers[port].currentCollision=m;
					msgs[m].next_collide=-1;
				}
				else {
					msgs[headers[port].currentCollision].next_collide=m;
					msgs[m].prev_collide=headers[port].currentCollision;
					headers[port].currentCollision=m;			
				}
			}
		}

		// advance to next message
		if (msgs[m].next<1 && a!=numActiveMsgs-1) cout << "ERROR1 in detect collions\n";
		else m = msgs[m].next;

	}

	// now look through headers to find collisions and call appropriate select function

	for (int b = 0; b < total_num_of_ports; b++){
		if (headers[b].numRequested>=1){
			m = headers[b].firstCollision;
			waiting=headers[b].numRequested;


			// set moves starting with first one
			for (int c=0; c < numVirts; c++){
				bool allEmpty=true;
				for (int x =0; x < bufferDepth; x ++){
					if (ports[b].o_buff[c*bufferDepth+x]!=0){
						allEmpty=false;
						x = bufferDepth+10;
					}
				}
				m = headers[b].firstCollision;
				// this lane is totally free for the taking.
				if (allEmpty) {
					ok=false;
					// port order
					if (select_function==0)	{ 
						// detect illegal routings, and correct
						int d;
						for (d =0; d < waiting; d++){
							if (WRAP && top_type==CUBE) {
								if (msgs[m].header_moved || (msgs[m].upper==1 && c<numVirts/2) || (msgs[m].upper==0  && c>=numVirts/2)) {
									if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
									if (m==0) cout << "ERROR2 in detect collision\n";
								}				
								else { 
									ok=true; 
									d=waiting; 
								}
							}
							else {
								if(!fLASH && !fMPLASH && !fALASH) 
								{
									if (msgs[m].header_moved)  {// advance if required
										if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
										if (m==0) cout << "ERROR3 in detect collision\n";
									}
									else {
										ok=true;
										d=waiting;
									}
								}
								else
								{
									if(fALASH && !fWIRELESS)
									{
										int layer_checked[4] = {0,0,0,0};
										for(int l = 0; l < numLayers; l++)
										{
											allEmpty = true;
											int prev_switch = (msgs[m].path[msgs[m].path_length-2]/numPorts) - numIps;
											int current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
											int destination_switch = msgs[m].dest[0];
											double best_commDens = -1;
											double commDens = 0;
											int bestLayer = -1;
											int bestPath = -1;
											if(prev_switch < 0)
												prev_switch += numIps;
											if(current_switch == destination_switch)
											{
												current_switch = msgs[m].source[0];
											}
											int pathnumber = msgs[m].pathNum;

											if(MultiPathLength[current_switch][destination_switch][0] == MultiPathLength[current_switch][destination_switch][pathnumber])
											{
												for(int j = numLayers-1; j >= 0 ; j--)
												{

													bool pastHistory = false;

													for(int i = 0; i < maxPaths; i++)
													{
														if(pathAllocLayer[prev_switch][destination_switch][i][j] ==  1 && MultiPathMsg[prev_switch][destination_switch][i][2] == (current_switch+numIps))
															pastHistory = true;
													}
													commDens = 0;

													if(pathAllocLayer[current_switch][destination_switch][pathnumber][j] == 1 && (msgs[m].vpath[msgs[m].path_length-1] == j || msgs[m].layer_history[j] == 0 || pastHistory == true) && layer_checked[j] == 0)
													{
														for (int i = 1; i < MultiPathLength[current_switch][destination_switch][pathnumber]-2; i++)
														{
															commDens += communication_density[MultiPathMsg[current_switch][destination_switch][pathnumber][i]][MultiPathMsg[current_switch][destination_switch][pathnumber][i+1]][msgs[m].layer];
														}
														if(bestLayer == -1 || (commDens) < best_commDens)
														{
															bestLayer = j;
															best_commDens = commDens;
															bestPath = pathnumber;
														}
													}
												}

											}
											if(bestLayer != -1)// && msgs[m].rerout == false)
											{
												layer_checked[bestLayer] = 1;
												msgs[m].layer = bestLayer;
												msgs[m].pathNum = bestPath;
												/*if(msgs[m].rerout == false)
												{
												msgs[m].sourceOrig = msgs[m].source[0];
												}*/
												msgs[m].source[0] = current_switch;
												msgs[m].rerout = true;
											}
											else
											{
												allEmpty = false;
												continue;
											}
											i = msgs[m].layer;
											for (int x =0; x < bufferDepth; x ++){
												if (ports[b].o_buff[i*bufferDepth+x]!=0){
													allEmpty=false;
													x = bufferDepth+10;
												}
											}
											if(allEmpty == true)
											{
												l = numLayers;
											}
										}
									}
									else if(fALASH && fWIRELESS)
									{
										int layer_checked[4] = {0,0,0,0};
										for(int l = 0; l < numLayers; l++)
										{
											allEmpty = true;
											int prev_switch = (msgs[m].path[msgs[m].path_length-2]/numPorts) - numIps;
											int current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
											int destination_switch = msgs[m].dest[0];
											double best_commDens = -1;
											double commDens = 0;
											int bestLayer = -1;
											int bestPath = -1;
											if(prev_switch < 0)
												prev_switch += numIps; 
											if(current_switch == destination_switch)
											{
												current_switch = msgs[m].source[0];
											}
											int pathnumber = msgs[m].pathNum;

											if(MultiPathLength[current_switch][destination_switch][pathnumber] != -1)
											{
												for(int j = numLayers-1; j >= 0 ; j--)
												{
													commDens = 0;

													bool pastHistory = false;

													for(int i = 0; i < maxPaths; i++)
													{
														if(pathAllocLayer[prev_switch][destination_switch][i][j] ==  1 && MultiPathMsg[prev_switch][destination_switch][i][2] == (current_switch+numIps))
															pastHistory = true;
													}

													if(pathAllocLayer[current_switch][destination_switch][pathnumber][j] == 1 && (msgs[m].vpath[msgs[m].path_length-1] == j || msgs[m].layer_history[j] == 0 || pastHistory == true) && layer_checked[j] == 0)
													{
														for (int i = 1; i < MultiPathLength[current_switch][destination_switch][pathnumber]-2; i++)
														{
															commDens += communication_density[MultiPathMsg[current_switch][destination_switch][pathnumber][i]][MultiPathMsg[current_switch][destination_switch][pathnumber][i+1]][j];
														}
														if(bestLayer == -1 || (commDens) < best_commDens)
														{
															bestLayer = j;
															best_commDens = commDens;
															bestPath = pathnumber;
														}
													}
												}

											}
											if(bestLayer != -1)// && msgs[m].rerout == false)
											{
												layer_checked[bestLayer] = 1;
												msgs[m].layer = bestLayer;
												msgs[m].pathNum = bestPath;
												/*if(msgs[m].rerout == false)
												{
												msgs[m].sourceOrig = msgs[m].source[0];
												}*/
												msgs[m].source[0] = current_switch;
												msgs[m].rerout = true;
											}
											else
											{
												allEmpty = false;
												continue;
											}
											i = msgs[m].layer;
											for (int x =0; x < bufferDepth; x ++){
												if (ports[b].o_buff[i*bufferDepth+x]!=0){
													allEmpty=false;
													x = bufferDepth+10;
												}
											}
											if(allEmpty == true)
											{
												l = numLayers;
											}
										}
									}
									else
									{
										allEmpty = true;
										i = msgs[m].layer;
										for (int x =0; x < bufferDepth; x ++){
											if (ports[b].o_buff[i*bufferDepth+x]!=0){
												allEmpty=false;
												x = bufferDepth+10;
											}
										}
									}
									if(msgs[m].header_moved || allEmpty == false) 
									{
										if(msgs[m].next_collide != - 1)
											m = msgs[m].next_collide;
										if(m==0) cout << "ERROR3 in detect collision\n";
									}
									else
									{
										ok = true;
										d=waiting;
										c = i;
									}
								}
							}
						}	
						// none was found
						if (ok==false && d==waiting) m = headers[b].firstCollision;
					}
					// oldest first
					else if (select_function==1) { 
						m = headers[b].firstCollision;	// start of list
						oldest_time = DUR;
						oldest_msg = m;
						for (int d=0; d< waiting; d++){
							if (!WRAP || ((msgs[m].upper==0 && c<numVirts/2) || (msgs[m].upper==1  && c>=numVirts/2))){
								if (msgs[m].start_time < oldest_time && !msgs[m].header_moved){
									oldest_time=msgs[m].start_time;
									oldest_msg=m;
									ok =true;
								}
							}
							if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
							if (m==0) cout << "ERROR in detect collision\n";						 
						} 
						m = oldest_msg;
					}
					// round robin
					else if (select_function==2){
						int e;
						m = headers[b].firstCollision; 
						// advance to the starting message
						for (e=0; e < cycles%numPorts; e++){
							if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
							else if (msgs[m].next_collide==-1) m = headers[b].firstCollision;
							if (m==0) cout << "ERROR in detect collision\n";	
						}
						for (e=0; e < waiting; e++){
							if (msgs[m].header_moved || (WRAP && (msgs[m].upper==1 && c<numVirts/2) || (msgs[m].upper==0  && c>=numVirts/2))){
								if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
								else if (msgs[m].next_collide==-1) m = headers[b].firstCollision;
								if (m==0) cout << "ERROR in detect collision\n";	
							}
							else {
								e=waiting;// exit loop if ready to go
								ok = true;
							}
						}
					}
					else if (select_function==3){
						m = headers[b].firstCollision; 
						highest_priority=-1;		
						highest_priority_msg=-1;
						// find highest priority
						for (int e=0; e < waiting; e++){
							if (!WRAP || ((msgs[m].upper==0 && c<numVirts/2) || (msgs[m].upper==1  && c>=numVirts/2))){
								if (max(msgs[m].priority,msgs[m].temp_priority)>highest_priority && !msgs[m].header_moved){
									highest_priority = max(msgs[m].priority,msgs[m].temp_priority);
									highest_priority_msg=m;
									ok = true;
								}
							}
							if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
							if (m==0) cout << "ERROR in detect collision\n";
						}
						m=highest_priority_msg;
					}
					if (ok) {
						ports[b].o_buff[c*bufferDepth]=-(m);		// this marker reserves the first space in the o_buff until the intranode moves are processed
						to_intranode_move_ports[intranode_moves]=b;
						to_intranode_move_oldports[intranode_moves]=msgs[m].path[msgs[m].path_length-1];	// should be current port
						to_intranode_move_flits[intranode_moves]=m+2*maxMessage;	// header token
						to_intranode_move_virts[intranode_moves]=c*bufferDepth;
						to_intranode_move_oldvirts[intranode_moves]=msgs[m].vpath[msgs[m].path_length-1]; 
						intranode_moves++;
						intranode_header_total++;
						temp_intranode_header_total++;
						ports[msgs[m].path[msgs[m].path_length-1]].sent_this_cycle_intra=true;
						// update message path
						msgs[m].path[msgs[m].path_length]=b;
						msgs[m].vpath[msgs[m].path_length]=c;
						if(fALASH)
						{
							msgs[m].path_history[msgs[m].path_length] = msgs[m].pathNum;
							msgs[m].layer_history[c] = 1;
						}
						msgs[m].header_moved=true;
						ports[msgs[m].path[msgs[m].path_length-1]].i_buff[msgs[m].vpath[msgs[m].path_length-1]*bufferDepth] = -m;	// leave marker to reserve buffer for rest of message
						msgs[m].path_length++;
						headers[b].numRequested--;


						if(headers[b].numRequested==0) c=numVirts;
						else if (headers[b].numRequested>0){
							if (msgs[m].next_collide!=-1) m = msgs[m].next_collide;		// go to next one.
							else if (msgs[m].next_collide==-1) m = headers[b].firstCollision;
							if (m==0) cout << "ErrOR in detect collision\n";
						}
						else cout << "numrequestd error in detect collisions\n";
					}
				}
			} // end for c-> numVirts
		}
	}
}




// Basic Turn around routing, Least common anscestor
int tree_route(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;
	nd = pt/numPorts;		//check this

	int level;
	if (top_type==BFT) level=find_level_bft(nd);
	else if (top_type==KARY) level=find_level_kary(nd);

	int numChildPorts;
	if (top_type==BFT) numChildPorts=4;
	if (top_type==KARY) numChildPorts=numPorts/2;

	if (m!=ports[pt].i_buff[buff] % maxMessage) cout << "ERROR in tree route at " << cycles << " msg " << m << " pt "<< pt << endl;

	if (pt%numPorts < numChildPorts) // if it's a child port
		return( nd*numPorts + route_from_child(nd, m, level));		
	else 		// it's a parent port
		return( nd*numPorts + msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[level-1]);				
}

int cube_route_mesh(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;		//check this
	get_cube_rel_addr(nd);  

	//tempAddr should be up to date

	// Dimension ordered routing, no wrap around links used
	// check if reached destination
	port=0;
	for (int d=0; d < dimensions; d++){
		// cycle through dimensions, check if at correct address
		if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d]!=tempAddr[d]){
			if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d]>tempAddr[d])
				port = nd*numPorts+2+2*d; // route to higher nodes
			else
				port = nd*numPorts+1+2*d; // route to lower nodes
			d = dimensions+1;	// exit routing loop
		}
	}
	if (port==0) port= nd*numPorts;	// destination reached

	return port;		// includes node
}

int cube_route_torus(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;		
	int gamma=0;	// numerical difference between dest and current node.  (dest-nd)
	int shortD=0;	// shortest distance including wraparound
	int wrap=0;		// wrap=1 use the wraparound links, wrap=0 don't
	//int upper=1;	// use upper vc band unless packet wraps around
	int dir=0;		// direction to be routed, 0=lower, 1=higher
	//int *tempAddr;
	//tempAddr = (int*) realloc (dimensions, sizeof(int));
	//tempAddr = (int*) realloc (tempAddr, dimensions*sizeof(int));
	get_cube_rel_addr(nd);
	// above update tempAddr
	if (m==19504 && cycles==537) 
		cycles =537;
	// check if reached destination
	if (get_cube_address(msgs[ports[pt].i_buff[buff] % (maxMessage)].dest) == nd-numIps) 
		return(nd*numPorts);

	// if dest. not reached, inspect/route address in order of dimensions
	for (int d=0; d < dimensions; d++){
		if (tempAddr[d]==msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d])		
			if (msgs[ports[pt].i_buff[buff] % (maxMessage)].dim==d){
				msgs[ports[pt].i_buff[buff] % (maxMessage)].dim++;	// store fact that dimension is 
				msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=1;  // reset to upper level for next dimension
			}
			if (tempAddr[d]!=msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d]){

				// route in dimension d
				gamma = msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d] - tempAddr[d];
				if ((cube_dimensions[d]-abs(gamma))>abs(gamma)) shortD = abs(gamma);
				else shortD=cube_dimensions[d]-abs(gamma);
				if (cube_dimensions[d]-abs(gamma)<abs(gamma)) wrap=1;
				else wrap=0;

				if (tempAddr[d]==0 && wrap==1)	// move to lower VCs
					msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;
				else if (tempAddr[d]==cube_dimensions[d]-1 && wrap==1)	// move to lower VCs
					msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;

				if (wrap==0){
					if (gamma>0)
						return(nd*numPorts+2+2*d);	// go up
					else
						return(nd*numPorts+1+2*d);	// go down
				}
				else {	// use wraparound
					if (gamma>0)
						return(nd*numPorts+1+2*d);	// go down, towards wraparound
					else
						return(nd*numPorts+2+2*d);	// go up, towards wraparound
				}
				d = dimensions;	// exit loop
			}

	}
}

int clustered_route_mesh(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;		//check this
	get_clustered_rel_addr(nd);  
	//tempAddr should be up to date

	// Dimension ordered routing, no wrap around links used
	// check if reached destination
	port=0;
	for (int d=0; d < dimensions; d++){
		// cycle through dimensions, check if at correct address
		if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d] != tempAddr[d]){
			if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d] > tempAddr[d])
				port = nd*numPorts+1+2*d; // route to higher nodes
			else
				port = nd*numPorts+0+2*d; // route to lower nodes
			d = dimensions+1;	// exit routing loop
		}
	}
	// destination reached
	if (port==0) port=	nd*numPorts +		// switch num
		(dimensions*2) +	// + ports taken by dimensions
		msgs[ports[pt].i_buff[buff] % maxMessage].dest[dimensions]; // + which IP we're going to

	return port;		// includes node
}

int clustered_route_torus(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;		
	int gamma=0;	// numerical difference between dest and current node.  (dest-nd)
	int shortD=0;	// shortest distance including wraparound
	int wrap=0;		// wrap=1 use the wraparound links, wrap=0 don't
	//int upper=1;	// use upper vc band unless packet wraps around
	int dir=0;		// direction to be routed, 0=lower, 1=higher
	//int *tempAddr;
	//tempAddr = (int*) realloc (dimensions, sizeof(int));
	//tempAddr = (int*) realloc (tempAddr, dimensions*sizeof(int));
	get_cube_rel_addr(nd);
	// above update tempAddr
	if (m==19504 && cycles==537) 
		cycles =537;
	// check if reached destination
	if (get_cube_address(msgs[ports[pt].i_buff[buff] % (maxMessage)].dest) == nd-numIps) {

		return	nd*numPorts +		// switch num
			(dimensions*2) +	// + ports taken by dimensions
			msgs[ports[pt].i_buff[buff] % maxMessage].dest[dimensions]; // + which IP we're going to
	}

	// if dest. not reached, inspect/route address in order of dimensions
	for (int d=0; d < dimensions; d++){
		if (tempAddr[d]==msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d])		
			if (msgs[ports[pt].i_buff[buff] % (maxMessage)].dim==d){
				msgs[ports[pt].i_buff[buff] % (maxMessage)].dim++;	// store fact that dimension is 
				msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=1;  // reset to upper level for next dimension
			}
			if (tempAddr[d]!=msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d]){

				// route in dimension d
				gamma = msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d] - tempAddr[d];
				if ((cube_dimensions[d]-abs(gamma))>abs(gamma)) shortD = abs(gamma);
				else shortD=cube_dimensions[d]-abs(gamma);
				if (cube_dimensions[d]-abs(gamma)<abs(gamma)) wrap=1;
				else wrap=0;

				if (tempAddr[d]==0 && wrap==1)	// move to lower VCs
					msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;
				else if (tempAddr[d]==cube_dimensions[d]-1 && wrap==1)	// move to lower VCs
					msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;

				if (wrap==0){
					if (gamma>0)
						return(nd*numPorts+1+2*d);	// go up
					else
						return(nd*numPorts+0+2*d);	// go down
				}
				else {	// use wraparound
					if (gamma>0)
						return(nd*numPorts+0+2*d);	// go down, towards wraparound
					else
						return(nd*numPorts+1+2*d);	// go up, towards wraparound
				}
				d = dimensions;	// exit loop
			}

	}
}

int stacked_route_mesh(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;
	bool in_bus=false;

	nd = pt/numPorts;		//check this

	if(nd >= (numIps+numSwitches)) { // This means we're in a bus
		in_bus = true;
		nd = (pt - (numIps+numSwitches)*numPorts)/num_layers; 
	}
	else
		get_stacked_rel_addr(nd);  

	//tempAddr should be up to date

	// Dimension ordered routing, no wrap around links used
	// check if reached destination
	port=0;
	if(!in_bus) {
		for (int d=0; d < dimensions; d++){
			// cycle through dimensions, check if at correct address
			if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d]!=tempAddr[d]){
				if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d]>tempAddr[d])
					port = nd*numPorts+2+2*d; // route to higher nodes
				else
					port = nd*numPorts+1+2*d; // route to lower nodes
				d = dimensions+1;	// exit routing loop
			}
		}
		if (port==0) {
			if(msgs[ports[pt].i_buff[buff] % maxMessage].dest[dimensions]!=tempAddr[dimensions]) //must move to bus
				port = nd*numPorts+dimensions*2+1; // route to bus
			else // We're at the destination
				port = nd*numPorts;	// destination reached
		}
	}
	else // in a bus, go to correct level
		port = (numIps+numSwitches)*numPorts+nd*num_layers+msgs[ports[pt].i_buff[buff] % maxMessage].dest[dimensions];

	return port;		// includes node
}

int stacked_route_torus(int m){
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;
	bool in_bus=false;

	int gamma=0;	// numerical difference between dest and current node.  (dest-nd)
	int shortD=0;	// shortest distance including wraparound
	int wrap=0;		// wrap=1 use the wraparound links, wrap=0 don't
	//int upper=1;	// use upper vc band unless packet wraps around
	int dir=0;		// direction to be routed, 0=lower, 1=higher

	nd = pt/numPorts;		//check this

	if(nd >= (numIps+numSwitches)) { // This means we're in a bus
		in_bus = true;
		nd = (pt - (numIps+numSwitches)*numPorts)/num_layers; 
	}
	else
		get_stacked_rel_addr(nd);  

	//int *tempAddr;
	//tempAddr = (int*) realloc (dimensions, sizeof(int));
	//tempAddr = (int*) realloc (tempAddr, dimensions*sizeof(int));
	// above update tempAddr
	if(!in_bus) {
		if (m==19504 && cycles==537) 
			cycles =537;
		// check if reached destination
		if (get_stacked_address(msgs[ports[pt].i_buff[buff] % (maxMessage)].dest) == nd-numIps) 
			return(nd*numPorts);

		// if dest. not reached, inspect/route address in order of dimensions
		for (int d=0; d < dimensions; d++){
			if (tempAddr[d]==msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d])		
				if (msgs[ports[pt].i_buff[buff] % (maxMessage)].dim==d){
					msgs[ports[pt].i_buff[buff] % (maxMessage)].dim++;	// store fact that dimension is 
					msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=1;  // reset to upper level for next dimension
				}
				if (tempAddr[d]!=msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d]){

					// route in dimension d
					gamma = msgs[ports[pt].i_buff[buff] % (maxMessage)].dest[d] - tempAddr[d];
					if ((cube_dimensions[d]-abs(gamma))>abs(gamma)) shortD = abs(gamma);
					else shortD=cube_dimensions[d]-abs(gamma);
					if (cube_dimensions[d]-abs(gamma)<abs(gamma)) wrap=1;
					else wrap=0;

					if (tempAddr[d]==0 && wrap==1)	// move to lower VCs
						msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;
					else if (tempAddr[d]==cube_dimensions[d]-1 && wrap==1)	// move to lower VCs
						msgs[ports[pt].i_buff[buff] % (maxMessage)].upper=0;

					if (wrap==0){
						if (gamma>0)
							return(nd*numPorts+2+2*d);	// go up
						else
							return(nd*numPorts+1+2*d);	// go down
					}
					else {	// use wraparound
						if (gamma>0)
							return(nd*numPorts+1+2*d);	// go down, towards wraparound
						else
							return(nd*numPorts+2+2*d);	// go up, towards wraparound
					}
					d = dimensions;	// exit loop
				}
		}
		// We must send to bus
		return nd*numPorts+dimensions*2+1; // route to bus
	}
	else
		return (numIps+numSwitches)*numPorts+nd*num_layers+msgs[ports[pt].i_buff[buff] % maxMessage].dest[dimensions];
}

void process_internode_moves(){
	for (int a = 0; a < internode_moves; a++){
		if(fDVFS)
		{
			if(to_internode_move_ports[a]/numPorts != msgs[to_internode_move_flits[a]%maxMessage].dest[0])
				sourceDestination << cycles << "\t" << (int) (to_internode_move_ports[a]/numPorts - numIps) << "\t" << msgs[to_internode_move_flits[a]%maxMessage].dest[0] << endl;
		}
		if(to_internode_move_oldports[a]/numPorts < numIps)
		{
			flitsPerLink[to_internode_move_oldports[a]/numPorts][to_internode_move_oldports[a]/numPorts]++;
			flitsInjected++;
		}
		else if(to_internode_move_ports[a]/numPorts < numIps)
		{
			flitsPerLink[to_internode_move_ports[a]/numPorts][to_internode_move_ports[a]/numPorts]++;
			flitsConsumed++;
		}
		else
		{
			if(fWIRELESS && connections[to_internode_move_ports[a]/numPorts][to_internode_move_oldports[a]/numPorts][0] != 'D')
			{
				wirelessUsage[to_internode_move_oldports[a]/numPorts-NUM_IPS]++;
			}
			else if(!fWIRELESS || connections[to_internode_move_ports[a]/numPorts][to_internode_move_oldports[a]/numPorts][0] == 'D')
			{
				flitsPerLink[to_internode_move_ports[a]/numPorts-NUM_IPS][to_internode_move_oldports[a]/numPorts-NUM_IPS]++;
			}
			flitsMoved++;
		}

		if(to_internode_move_flits[a] > 2*maxMessage) //It's a header
		{
			if(!fMESH)
			{
				if(numRepeaters[to_internode_move_oldports[a]/numPorts][to_internode_move_ports[a]/numPorts] > 0)
				{
					msgs[to_internode_move_flits[a]%maxMessage].wait = numRepeaters[to_internode_move_oldports[a]/numPorts][to_internode_move_ports[a]/numPorts];
				}
			}
		}

		ports[to_internode_move_ports[a]].i_buff[to_internode_move_virts[a]] = to_internode_move_flits[a];
		ports[to_internode_move_oldports[a]].last_virt_sent=to_internode_move_oldvirts[a];
		communicationTotal++;
		flits_between_switches[to_internode_move_oldports[a]/numPorts][to_internode_move_ports[a]/numPorts]++; //sourav for flits count between switches
		if(fALASH)
			communicationPerLink[to_internode_move_oldports[a]/numPorts][to_internode_move_ports[a]/numPorts][to_internode_move_virts[a]]++;
		if(connections[to_internode_move_ports[a]/numPorts][to_internode_move_oldports[a]/numPorts][0] != 'D' && fWIRELESS)
		{
			if(to_internode_move_flits[a] > 2*maxMessage)
				wirelesstaken++;
			wireless_usage++;
			msgs[to_internode_move_flits[a]%maxMessage].wireless = true;
		}
		if (to_internode_move_flits[a]>2*maxMessage) // if a header, 
			msgs[to_internode_move_flits[a]%maxMessage].header_in=true;
	}
	internode_moves=0;			// reset counter for next cycle
}

void process_intranode_moves() {
	for (int a = 0; a < intranode_moves; a++){
		ports[to_intranode_move_ports[a]].o_buff[to_intranode_move_virts[a]] = to_intranode_move_flits[a];
		ports[to_intranode_move_oldports[a]].last_virt_sent_intra=to_intranode_move_oldvirts[a];
		if (to_intranode_move_flits[a]>2*maxMessage) // if a header, 
		{
			msgs[to_intranode_move_flits[a]%maxMessage].header_in=false;
			if((to_intranode_move_ports[a]/numPorts) != (msgs[to_intranode_move_flits[a]%maxMessage].sourceOrig+NUM_IPS) && (to_intranode_move_ports[a]/numPorts) != (msgs[to_intranode_move_flits[a]%maxMessage].dest[0]+NUM_IPS))
			{
				msgs[to_intranode_move_flits[a]%maxMessage].wait = (routerStages-1);
			}
		}
	}

	intranode_moves=0;			// reset counter for next cycle
}


// advnace through tracefile and create messages if appropriate time
void process_trace_injections(){

	if (! traceFile)
	{
		cout << "Error opening input file" << endl;
	}

	// do initial load of values
	if (cycles==0) traceFile >> numTraces >> tr_time >> tr_src;

	bool go=true;
	while (go) {
		if (tr_time==cycles) {
			// create message from src last_src
			tr_counter++;
			inject_from_trace(tr_src);
			tr_input=true;
			arrival_histogram[cycles/100]++;
			if (DUMP) messagesFile << "***** NEW MESSAGE ARRIVED AT T:" << cycles << " SOURCE: " << tr_src << endl;
			tr_msgs++;
			traceFile >> tr_time >> tr_src;
			if (tr_counter>=numTraces) {
				tr_input=false;
				tr_time=-1;
				DUR=cycles;	// end simulation
			}
		}
		else {
			go=false;
		}
	}
}

void inject_from_trace(int src){

	if (src==numIpsUsed) src= int_rand(64);
	if (src<0 || src>=numIpsUsed) cout << "error in inject from trace.  receiced src: " << src << endl;

	if (ips[src].queue_pop!=queueSize-1){
		ips[src].queue[ips[src].queue_pop]=cycles;
		ips[src].queue_pop++;
	}
	else { 
		if (SAT==0){
			cout << "QUEUE OVERLOAD AT T: " << cycles << " SOURCE: " << src << endl;
			cycles=DUR+10;
			//Z=500;
			// interupt program here
		}
	}
}
// create new messages if neccessary
// if output buffer of generating node empty, decrease the gen count and put a flit in there.
void process_injections() {
	bool ok;
	float r; // random number
	bool doneThisVirt;
	bool allEmpty=true;
	bool arrival;
	int this_port;
	float next_change;


	for (int a = 0; a < numIpsUsed; a++)
	{
		arrival=false;
		this_port = a*numPorts + inject_port;

		// below determines if a new message has arrived 
		if(!fBENCHMARK)
		{
			// Self-similar traffic injection
			if(injection_type==SS) {
				if(ips[a].next_arrival == cycles) {
					arrival = true;
					if((ips[a].next_state_change - cycles) >= (float)msgl*SS_MULTIPLIER/load )
						ips[a].next_arrival = cycles +(int) ( (float)msgl*SS_MULTIPLIER/load );
				}
				if(ips[a].next_state_change == cycles) { // We're changing from ON to OFF or vice versa
					if(ips[a].is_on != 0) { // is ON, will now turn OFF
						ips[a].is_on = 0;   // turn OFF
						next_change =  pow((float_rand(1)),float(-1.0/1.25));  // Pareto Distribution  (6/1 Kevin: modified[(-1.0/1.25) to float(-1.0/1.25)])
						if(next_change <= 0)
							next_change = 1;
						ips[a].next_state_change = cycles + (int) (((next_change*(float)msgl+0.5))*SS_MULTIPLIER/load);  // Find length of state

					}
					else { // is OFF, will now turn ON
						ips[a].is_on = 1;   // turn ON
						arrival = true;     // send a message
						next_change =  pow((float_rand(1)),float(-1.0/1.25));  // Pareto Distribution  (6/1 Kevin: modified[(-1.0/1.25) to float(-1.0/1.25)])
						ips[a].next_state_change = cycles + (int) (((next_change+0.5)*(float)msgl)*SS_MULTIPLIER/load); // Find length of state
						if( (ips[a].next_state_change - cycles) >= 2*((float)msgl*SS_MULTIPLIER/load) )
							ips[a].next_arrival = cycles + (int) ((float)msgl*SS_MULTIPLIER/load);  // Set up next message if applicable
					}
				}
			}
			// Poisson Traffic Injection
			if (injection_type==POISSON) 
			{
				if (!USETRACE && ips[a].next_arrival==-1)
				{
					if(load <= 1.0)
					{
						ips[a].next_arrival=(int) get_exp_dist(msgl/load) + cycles;
					}
					else
					{
						//ips[a].next_arrival=(int) get_exp_dist(msgl/load) + cycles;
						//ips[a].next_arrival=(int) get_exp_dist(msgl/benchmarkLoad[a]) + cycles;
						double injection = rand() / RAND_MAX;
						if(injection < benchmarkLoad[a])
						{
							ips[a].next_arrival = 1 + cycles;
						}
					}
				}
				// check if arrival occurs this cycle
				//cout << "Next arrival: " << ips[a].next_arrival << " Cycle: " << cycles << endl;
				if (ips[a].next_arrival==cycles && !USETRACE){
					//cerr << cycles << endl;
					arrival=true;
					ips[a].next_arrival=-1;
					tr_msgs++;	// increase injection counter
					arrival_histogram[cycles/100]++;
					if (DUMP) messagesFile << "***** NEW MESSAGE ARRIVED AT T:" << cycles << " SOURCE: " << a << endl;
				}
			}
		}
		else //fBENCHMARK
		{
			if(ips[a].next_arrival == -1)
			{
				if(fLATENCY)
					ips[a].next_arrival=(int) get_exp_dist(msgl/fijMatrixSum[a]) + cycles;
				if(fPOWER)
				{
					// double temp = rand(); // bug: integer overflow
					// temp = temp/(RAND_MAX+1); // bug: integer overflow
					double temp = ((double)rand()) / ((double)RAND_MAX+1); // yuchen: bug fixed

					if(temp < fijMatrixSum[a])
					{
						ips[a].next_arrival = 1 + cycles;
					}
				}
			}
			if(ips[a].next_arrival == cycles)
			{
				arrival=true;
				ips[a].next_arrival=-1;
				tr_msgs++;	// increase injection counter
				if (ips[a].queue_pop!=queueSize-1)
				{
					ips[a].queue[ips[a].queue_pop]=cycles;
					double temp;
					// temp = ((double)rand() / (RAND_MAX+1)); // latency bug: integer overflow
					// cout << "old random number: " << temp << endl;
					temp = ((double)rand()) / ((double)RAND_MAX+1); // yuchen: bug fixed
					// cout << "new random number:" << temp << endl;
					// assert(false);
					int i = 0;
					temp *= fijMatrixSum[a];
					for(i = 0; i < numIps; i++)
					{
						if(a != i)
						{
							temp -= fijMatrix[a][i];
							if(temp <= 0)
								break;
						}
					}
					ips[a].queue_dest[ips[a].queue_pop]=i;
					ips[a].queue_pop++;
				}
				else
				{
					int dummy = rand();
				}
								
				arrival = false;
			}
		}

		for (int b = 0; b < numVirts; b++)
		{
			doneThisVirt=false;
			allEmpty=true;
			for (int i = 0; i < bufferDepth; i++)
			{
				if (ports[this_port].o_buff[b*bufferDepth+i]!=0) 
				{ // if next output buffer is empty	
					allEmpty=false;	
				}
			}
			// skip gateway nodes
			if (top_type==OCTO5 && (a==0 || a==8 || a==16 || a==24))
			{
				doneThisVirt=true;
			}

			if (doneThisVirt==false) 
			{ 

				if (ips[a].generate[b] == 0 && allEmpty==true) 
				{	// if ip is ready to send, and there is a free virt

					if (ips[a].queue_pop>0) 
					{ // if there is a message waiting

						ips[a].generate[b] = msgl-1;
						ok = false;
						// check for duplicates of msg still existing in network
						while (ok==false) 
						{
							if (msgs[msgIndex].end_time==-2) 
							{	// this message still exists
								msgIndex++;		// skip this index
								if (msgIndex==maxMessage-1) 
								{
									msgIndex=1;
								}
							}
							else ok = true;
						}

						ips[a].generate_msgs[b] = msgIndex;
						ports[this_port].o_buff[b*bufferDepth] = msgIndex + 2*maxMessage;   // place header flit in o_buff

						if(!fBENCHMARK)
						{
							if(load <= 1.0)
							{
								generate_source_and_dest(msgIndex,a);
							}
							else
							{
								//INSERT BENCHMARK STUFF HERE
								generate_source_and_dest(msgIndex, a);
							}
						}
						else
						{
							if(fALASH)
								msgs[msgIndex].source[0] = a;
							else
							{
								msgs[msgIndex].source[0] = a % (int) sqrt(NUM_IPS);
								msgs[msgIndex].source[1] = a / (int) sqrt(NUM_IPS);
							}
							msgs[msgIndex].path[0] = a*numPorts + inject_port;
							msgs[msgIndex].path_length = 1;
							msgs[msgIndex].upper = 1;
							msgs[msgIndex].end_time = -2;

							msgs[msgIndex].start_network = -1;
							
							if(fALASH)
								msgs[msgIndex].dest[0] = ips[a].queue_dest[0];
							else
							{
								if(dimensions == 3)
								{
									msgs[msgIndex].dest[2] = ips[a].queue_dest[0] / 16;
									msgs[msgIndex].dest[1] = (ips[a].queue_dest[0] % 16) / 4;
									msgs[msgIndex].dest[0] = (ips[a].queue_dest[0] % 16) % 4;
								}
								else if(dimensions == 2)
								{
									msgs[msgIndex].dest[0] = ips[a].queue_dest[0] %  (int) sqrt(NUM_IPS);
									msgs[msgIndex].dest[1] = ips[a].queue_dest[0] / (int) sqrt(NUM_IPS);
								}
							}
							messagesInjected[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]]++;
						}

						msgs[msgIndex].path[0] = this_port;   // store starting port in path
						msgs[msgIndex].path_length = 1;
						msgs[msgIndex].start_time = ips[a].queue[0];  // head of queue
						// reset queue
						for (int q=0; q < queueSize-1; q++){
							ips[a].queue[q]=ips[a].queue[q+1];
							ips[a].queue_dest[q] = ips[a].queue_dest[q+1];
						}
						ips[a].queue[queueSize-1]=-1;
						ips[a].queue_pop--;

						msgs[msgIndex].end_time = -2;  //active
						msgs[msgIndex].header_in=false;
						msgs[msgIndex].header_done=false;
						msgs[msgIndex].header_moved=false;
						msgs[msgIndex].next=-1;
						msgs[msgIndex].next_collide=-1;
						add_msg_to_list(msgIndex);
						//msgs[msgIndex].priority=int_rand(4);	// assigns 0-3 prioirty to msg
						msgs[msgIndex].global_pathNumber = -1;
						msgs[msgIndex].bw = 2;
						msgs[msgIndex].wait = -1;
						msgs[msgIndex].wireless = false;
						msgs[msgIndex].start_network = -1;
						msgs[msgIndex].end_network = -1;
						
						if(fLASH || fMPLASH || fALASH)
						{
							msgs[msgIndex].rerout = false;
							msgs[msgIndex].sourceOrig = msgs[msgIndex].source[0];
							msgs[msgIndex].layer_history[0] = 0;
							msgs[msgIndex].layer_history[1] = 0;
							msgs[msgIndex].layer_history[2] = 0;
							msgs[msgIndex].layer_history[3] = 0;
							if(fMPLASH)
							{
								msgs[msgIndex].pathNum = determine_path(msgIndex);
								if(msgs[msgIndex].pathNum != 0)
								{
									printf("Different Path taken\n");
								}
							}
							else if(fLASH)
							{
								if(fWIRELESS)
								{
									if(pathLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] == -1 || MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] == -1)
									{
										msgs[msgIndex].pathNum = 0;
										msgs[msgIndex].rerout = true;
									}
									else
									{
										msgs[msgIndex].pathNum = 1;
										total_wireless++;
									}
								}
								else
									msgs[msgIndex].pathNum = 0;
							}
							if(fALASH)
							{
								if(fWIRELESS)
								{
									if(MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][wirelessPathNum] == -1)
									{
										msgs[msgIndex].rerout = true;
									}
									double best_commDens = -1;
									double commDens = 0;
									int bestLayer = -1;
									int bestPath  = -1;

									for(int pathnumber = (maxPaths - 1)  ; pathnumber >= 0; pathnumber--)
									{
										for(int j = numLayers-1; j >= 0 ; j--)
										{
											commDens = 0;
											if(pathAllocLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][j] == 1)
											{
												for (int i = 1; i < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber]-2); i++)
												{
													commDens += communication_density[MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][i]][MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][i+1]][j];
												}
												if(bestLayer == -1 || commDens < best_commDens)
												{
													bestLayer = j;
													best_commDens = commDens;
													bestPath = pathnumber;
												}
											}
										}
									}
									msgs[msgIndex].pathNum = bestPath;
									msgs[msgIndex].layer = bestLayer;
								}
								else
								{
									double best_commDens = -1;
									double commDens = 0;
									int bestLayer = -1;
									int bestPath;

									for(int pathnumber =0  ; pathnumber < maxPaths; pathnumber++)
									{
										for(int j = numLayers-1; j >= 0 ; j--)
										{
											commDens = 0;
											if(pathAllocLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][j] == 1)
											{
												for (int i = 1; i < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber]-2); i++)
												{
													commDens += communication_density[MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][i]][MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][i+1]][j];
												}
												if(bestLayer == -1 || commDens < best_commDens)
												{
													bestLayer = j;
													best_commDens = commDens;
													bestPath = pathnumber;
												}
											}
										}
									}
									msgs[msgIndex].pathNum = bestPath;
									msgs[msgIndex].layer = bestLayer;
								}
							}
							else
							{
								msgs[msgIndex].layer = pathLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][msgs[msgIndex].pathNum];
							}
						}
						if(msgs[msgIndex].pathNum == wirelessPathNum)
							doneThisVirt = true;
						doneThisVirt=true;

						if (DUMP && top_type==CUBE) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_cube_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==CLUSTERED) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_clustered_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==STACKED) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_stacked_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==BFT && numNodes==92) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[2]*16+msgs[msgIndex].dest[1]*4+ msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==KARY && numIps==64) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[2] << " , " << msgs[msgIndex].dest[1] << " , " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==BFT && numNodes==376) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " (" << msgs[msgIndex].source[3] << "," << msgs[msgIndex].source[2] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[0] << ") dest: (" << msgs[msgIndex].dest[3] << "," << msgs[msgIndex].dest[2] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[0] << ")" << endl;
						if (DUMP && top_type==BFT && numNodes==1520) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << " started: " <<  msgs[msgIndex].start_time  << " source: " << a << " (" << msgs[msgIndex].source[4] << msgs[msgIndex].source[3] << "," << msgs[msgIndex].source[2] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[0] << ") dest: (" << msgs[msgIndex].dest[4] << msgs[msgIndex].dest[3] << "," << msgs[msgIndex].dest[2] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[0] << ")" << endl;
						if (DUMP && top_type==RING) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTO) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTO5) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << endl;
						if (DUMP && top_type==OCTOM) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << "started: " <<  msgs[msgIndex].start_time << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << endl;
						if (DUMP && top_type==SUPERS) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTOM3) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[2] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[2] <<  endl;
						else if (DUMP && top_type==BFT) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: "  << msgs[msgIndex].dest[0] << endl;
						msgIndex++;	
						if (msgIndex==maxMessage-1) {
							/*			// do check print oldest message
							int lowest = maxMessage+1;
							for (int g = 0; g < numPorts*numNodes; g++){
							for (int m = 0; m < numVirts; m++){
							if (ports[g].i_buff[m] < lowest && ports[g].i_buff[m] > 0) lowest = ports[g].i_buff[m];
							if (ports[g].o_buff[m] < lowest && ports[g].o_buff[m] > 0) lowest = ports[g].o_buff[m];
							}
							}
							cout << "lowest: " << lowest << endl;*/
							msgIndex=1;		// reset index once max is reached

						}	
					} // end if queue_pop >0

					// queue is empty, but an arrival has happened this cycle
					else if (arrival ==true)
					{						

						arrival =false; // set arrival to false once it has been assigned a virtual channel
						ips[a].generate[b] = msgl-1;
						ok = false;
						//////////////////////////////////////
						//cerr << "Message index is: " << msgIndex;
						// check for duplicates of msg still existing in network
						while (ok==false) {
							if (msgs[msgIndex].end_time==-2) {	// this message still exists
								msgIndex++;		// skip this index
								if (msgIndex==maxMessage-1) msgIndex=1;
							}
							else ok = true;
						}
						//////////////////////////////////////
						ips[a].generate_msgs[b] = msgIndex;
						ports[this_port].o_buff[b*bufferDepth] = msgIndex + 2*maxMessage;   // place header flit in o_buff

						msgs[msgIndex].path[0] = this_port;   // store starting port in path
						msgs[msgIndex].path_length = 1;
						msgs[msgIndex].start_time = cycles;
						msgs[msgIndex].upper=1;
						msgs[msgIndex].header_in=false;
						msgs[msgIndex].header_done=false;
						msgs[msgIndex].header_moved=false;
						msgs[msgIndex].next=-1;
						msgs[msgIndex].next_collide=-1;
						//msgs[msgIndex].priority=int_rand(4);	// assigns 0-3 prioirty to msg
						msgs[msgIndex].global_pathNumber = -1;
						msgs[msgIndex].end_time = -2;  //active
						msgs[msgIndex].bw = 2;
						msgs[msgIndex].wait = -1;
						msgs[msgIndex].wireless = false;
						msgs[msgIndex].start_network = -1;
						msgs[msgIndex].end_network = -1;
						add_msg_to_list(msgIndex);

						if(!fBENCHMARK)
						{
							if(load <= 1.0)
							{
								generate_source_and_dest(msgIndex,a);
							}
							else
							{
								//INSERT BENCHMARK STUFF HERE
								generate_source_and_dest(msgIndex, a);
							}
						}
						else
						{
							if(fALASH)
								msgs[msgIndex].source[0] = a;
							else
							{
								msgs[msgIndex].source[0] = a % (int) sqrt(NUM_IPS);
								msgs[msgIndex].source[1] = a / (int) sqrt(NUM_IPS);
							}
							msgs[msgIndex].path[0] = a*numPorts + inject_port;
							msgs[msgIndex].path_length = 1;
							msgs[msgIndex].upper = 1;
							msgs[msgIndex].end_time = -2;
							msgs[msgIndex].end_network = -1;
							// double temp = ((double)rand() / (RAND_MAX+1)); // bug: integer overflow
							double temp = ((double)rand()) / ((double)RAND_MAX+1); // yuchen: bug fixed
							int i = 0;
							temp *= fijMatrixSum[a];
							for(i = 0; i < numIps; i++)
							{
								if(a != i)
								{
									temp -= fijMatrix[a][i];
									if(temp <= 0)
										break;
								}
							}
							if(fALASH)
								msgs[msgIndex].dest[0] = i;
							else
							{
								msgs[msgIndex].dest[0] = i % (int) sqrt(NUM_IPS);
								msgs[msgIndex].dest[1] = i / (int) sqrt(NUM_IPS);
							}
							msgs[msgIndex].dest[0] = i;
							messagesInjected[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]]++;
						}
						if(fLASH || fMPLASH || fALASH)
						{
							msgs[msgIndex].rerout = false;
							msgs[msgIndex].sourceOrig = msgs[msgIndex].source[0];
							msgs[msgIndex].layer_history[0] = 0;
							msgs[msgIndex].layer_history[1] = 0;
							msgs[msgIndex].layer_history[2] = 0;
							msgs[msgIndex].layer_history[3] = 0;
							if(fMPLASH)
							{
								msgs[msgIndex].pathNum = determine_path(msgIndex);
								if(msgs[msgIndex].pathNum != 0)
								{
									printf("Different Path taken\n");
								}
							}
							else if(fALASH)
							{
								msgs[msgIndex].pathNum = 0;
							}
							else
							{
								if(fWIRELESS)
								{
									if(pathLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] == -1 || MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] == -1)
									{
										msgs[msgIndex].pathNum = 0;
										msgs[msgIndex].rerout = true;
									}
									else
									{
										msgs[msgIndex].pathNum = 1;
										total_wireless++;
									}
								}
								else
									msgs[msgIndex].pathNum = 0;
							}
							if(fALASH)
							{
								if(fWIRELESS)
								{
									if(MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] != -1)
									{
										int wi_switch = 0;
										int i = 0;
										for(i = 0;  i < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1]-2); i++)
										{
											if(connections[MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1][i]][MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1][i+1]][0] != 'D')
												break;
										}
										wi_switch = MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1][i] - numIps;
										if((MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0] + 2) < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][1] + MultiPathLength[wi_switch][msgs[msgIndex].dest[0]][0]-3))
											msgs[msgIndex].rerout = true;

									}
									double best_commDens = -1;
									double commDens = 0;
									int bestLayer = -1;
									int bestPath = 0;

									for(int pathnumber =0  ; pathnumber < maxPaths; pathnumber++)
									{
										for(int j = numLayers-1; j >= 0 ; j--)
										{
											commDens = 0;
											if(pathAllocLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][j] == 1)
											{
												for (int i = 1; i < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0]-2); i++)
												{
													commDens += communication_density[MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0][i]][MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0][i+1]][j];
												}
												if(bestLayer == -1 || commDens < best_commDens)
												{
													bestLayer = j;
													best_commDens = commDens;
													bestPath = pathnumber;
												}
											}
										}
									}
									msgs[msgIndex].pathNum = bestPath;
									msgs[msgIndex].layer = bestLayer;
								}
								else
								{
									double best_commDens = -1;
									double commDens = 0;
									int bestLayer = -1;
									int bestPath;

									for(int pathnumber =0  ; pathnumber < maxPaths; pathnumber++)
									{
										for(int j = numLayers-1; j >= 0 ; j--)
										{
											commDens = 0;
											if(pathAllocLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][pathnumber][j] == 1)
											{
												for (int i = 1; i < (MultiPathLength[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0]-2); i++)
												{
													commDens += communication_density[MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0][i]][MultiPathMsg[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][0][i+1]][j];
												}
												if(bestLayer == -1 || commDens < best_commDens)
												{
													bestLayer = j;
													best_commDens = commDens;
													bestPath = pathnumber;
												}
											}
										}
									}
									msgs[msgIndex].pathNum = bestPath;
									msgs[msgIndex].layer = bestLayer;
								}
							}
							else
							{
								msgs[msgIndex].layer = pathLayer[msgs[msgIndex].source[0]][msgs[msgIndex].dest[0]][msgs[msgIndex].pathNum];
							}
						}
						if(msgs[msgIndex].pathNum == wirelessPathNum)
							doneThisVirt = true;
						doneThisVirt=true;

						if (DUMP && top_type==CUBE) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_cube_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==CLUSTERED) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_clustered_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==STACKED) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << get_stacked_address(msgs[msgIndex].dest) << endl;
						if (DUMP && top_type==BFT && numNodes==92) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[2]*16+ msgs[msgIndex].dest[1]*4+ msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==KARY && numIps==64) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[2] << " , " << msgs[msgIndex].dest[1] << " , " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==BFT && numNodes==376) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " (" << msgs[msgIndex].source[3] << "," << msgs[msgIndex].source[2] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[0] << ") dest: (" << msgs[msgIndex].dest[3] << "," << msgs[msgIndex].dest[2] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[0] << ")" << endl;
						if (DUMP && top_type==BFT && numNodes==1520) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << a << " (" << msgs[msgIndex].source[4] << msgs[msgIndex].source[3] << "," << msgs[msgIndex].source[2] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[0] << ") dest: (" << msgs[msgIndex].dest[4] << msgs[msgIndex].dest[3] << "," << msgs[msgIndex].dest[2] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[0] << ")" << endl;
						if (DUMP && top_type==RING) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTO) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTO5) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << endl;
						if (DUMP && top_type==OCTOM) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << "started: " <<  msgs[msgIndex].start_time << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << endl;
						if (DUMP && top_type==SUPERS) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[0] << endl;
						if (DUMP && top_type==OCTOM3) messagesFile << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles << "started: " <<  msgs[msgIndex].start_time  << " source: " << msgs[msgIndex].source[0] << "," << msgs[msgIndex].source[1] << "," << msgs[msgIndex].source[2] << " dest: " << msgs[msgIndex].dest[0] << "," << msgs[msgIndex].dest[1] << "," << msgs[msgIndex].dest[2] <<  endl;
						else if (DUMP && top_type==BFT) messagesFile << endl << "***** NEW MESSAGE " << msgIndex << " at time: " << cycles  << " started: " <<  msgs[msgIndex].start_time << " source: " << a << " dest: " << msgs[msgIndex].dest[1] << " "  << msgs[msgIndex].dest[0] << endl;
						msgIndex++;	
						if (msgIndex==maxMessage-1) {
							/*			// do check print oldest message
							int lowest = maxMessage+1;
							for (int g = 0; g < numPorts*numNodes; g++){
							for (int m = 0; m < numVirts; m++){
							if (ports[g].i_buff[m] < lowest && ports[g].i_buff[m] > 0) lowest = ports[g].i_buff[m];
							if (ports[g].o_buff[m] < lowest && ports[g].o_buff[m] > 0) lowest = ports[g].o_buff[m];
							}
							}
							cout << "lowest: " << lowest << endl;*/
							msgIndex=1;		// reset index once max is reached
						}
					}

				}
			}

			if (doneThisVirt==false && ips[a].generate[b] > 0) 
			{
				for (int x =0 ; x < bufferDepth; x++)
				{	
					if (ports[this_port].o_buff[b*bufferDepth+x]==0 || ports[this_port].o_buff[b*bufferDepth+x] == -ips[a].generate_msgs[b]) 
					{ // ip is generating, o_buff is empty
						ips[a].generate[b]--;
						ports[this_port].o_buff[b*bufferDepth+x]=ips[a].generate_msgs[b];
						doneThisVirt=true;
						if (ips[a].generate[b]==0) 
						{
							ports[this_port].o_buff[b*bufferDepth+x]=ips[a].generate_msgs[b] + maxMessage;	// tail flits in the range 1025-2048
							ips[a].generate_msgs[b]=0;		// reset generating message
						}
					}
				}
			}
		} // end for virts

		// check if arrival still flagged, if so, add to queue
		if (arrival==true){
			if (ips[a].queue_pop!=queueSize-1){
				ips[a].queue[ips[a].queue_pop]=cycles;
				if(fBENCHMARK)
					ips[a].queue_dest[ips[a].queue_pop]=rand();
				ips[a].queue_pop++;
			}
			else {
				if (SAT==0){
					cout << "QUEUE OVERLOAD AT T: " << cycles << " SOURCE: " << a << endl;
					//cycles=DUR+10;
					DUR=cycles;
					//Z=500;
					// interupt program here
				}
			}
		}
	}	// end for ips
}	// end fuction

void generate_source_and_dest(int i, int a){
	float r; // random number
	int n;

	if (top_type == BFT||top_type==KARY)
	{
		//msgs[msgIndex].end_time = -2;  //active
		//add_msg_to_list(msgIndex);
		if (numIps==64) {
			msgs[i].source[0]=a%4;
			msgs[i].source[1]=(a%16)/4;
			msgs[i].source[2]=a/16;

			msgs[i].dest[0]=a%4;
			msgs[i].dest[1]=(a%16)/4;
			msgs[i].dest[2]= a/16;
		}
		else if (numIps==256){
			msgs[i].source[0]=a%4;
			msgs[i].source[1]=(a%16)/4;
			msgs[i].source[2]=(a%64)/16;
			msgs[i].source[3]=a/64;

			msgs[i].dest[0]=a%4;
			msgs[i].dest[1]=(a%16)/4;
			msgs[i].dest[2]= (a%64)/16;
			msgs[i].dest[3]= a/64;	
		}
		else if (numIps==1024)
		{
			msgs[i].source[0]=a%4;
			msgs[i].source[1]=(a%16)/4;
			msgs[i].source[2]=(a%64)/16;
			msgs[i].source[3]=(a%256)/64;
			msgs[i].source[4]=a/256;

			msgs[i].dest[0]= a%4;
			msgs[i].dest[1]=(a%16)/4;
			msgs[i].dest[2]= (a%64)/16;
			msgs[i].dest[3]= (a%256)/64;	
			msgs[i].dest[4]= a/256;
		}
		else if (numIps==16) {
			msgs[i].source[0]=a%4;
			msgs[i].source[1]=a/4;

			msgs[i].dest[0]=a%4;
			msgs[i].dest[1]=a/4; 
		}
		else if (numIps==4) {
			msgs[i].source[0]=a;
			msgs[i].dest[0]=a;
		}
		// generate destination

		// uniform random traffic , or trace	
		if (traffic==0)	{  
			if (numIps==64){
				while (msgs[i].dest[0]==a%4 && msgs[i].dest[1]== (a%16)/4 && msgs[i].dest[2] == a/16){
					msgs[i].dest[0]=int_rand(4);	// randomly choose destination
					msgs[i].dest[1]=int_rand(4);
					msgs[i].dest[2]=int_rand(4);
				}
			}
			else if (numIps==256){
				while (msgs[i].dest[0]==a%4 && msgs[i].dest[1]== (a%16)/4 && msgs[i].dest[2] == (a%64)/16 && msgs[i].dest[3]==a/64){
					msgs[i].dest[0]=int_rand(4);
					msgs[i].dest[1]=int_rand(4);
					msgs[i].dest[2]=int_rand(4);
					msgs[i].dest[3]=int_rand(4);
				}
			}
			else if (numIps==1024){
				while (msgs[i].dest[0]==a%4 && msgs[i].dest[1]== (a%16)/4 && msgs[i].dest[2] == (a%64)/16 && msgs[i].dest[3]==(a%256)/64 && msgs[i].dest[4] == a/256){
					msgs[i].dest[0]=int_rand(4);
					msgs[i].dest[1]=int_rand(4);
					msgs[i].dest[2]=int_rand(4);
					msgs[i].dest[3]=int_rand(4);
					msgs[i].dest[4]=int_rand(4);
				}
			}
			else if (numIps==16){
				while (msgs[i].dest[0]==a%4 && msgs[i].dest[1]== a/4){
					msgs[i].dest[0]=int_rand(4);
					msgs[i].dest[1]=int_rand(4);
				}
			}
			else if (numIps==4){
				while (msgs[i].dest[0]==a){
					msgs[i].dest[0]=int_rand(4);
				}
			}
		}
		// complement traffic
		else if (traffic==1) {
			if (numIps==64)
				for (int c = 0; c < 3; c++)
					msgs[i].dest[c]=3-msgs[i].dest[c];		
			else if (numIps==256)
				for (int c = 0; c < 4; c++)
					msgs[i].dest[c]=3-msgs[i].dest[c];		
			else if (numIps==16)
				for (int c = 0; c < 2; c++)
					msgs[i].dest[c]=3-msgs[i].dest[c];		
			/*for (int c = 0; c < 2; c++)
			msgs[i].dest[c]=3-msgs[i].dest[c];*/
		}
		// hotspot traffic
		else if (traffic==2) {
			int *hDest;
			hDest = (int*) calloc(levels,sizeof(int));
			r = float_rand(100);
			//if going to hotspot
			if (r<hotPercent) {
				int h = (int)(r/(hotPercent/numHotspots));	// number of specific hotspot
				//hDest = get_bft_rel_addr(hotspots[h]);
				get_bft_rel_addr(hotspots[h]);
				msgs[i].dest=tempAddr;
			}
			//if going to a non-hotspot
			else {
				int out = 1;
				while (out==1) {
					out = 0;
					r = float_rand(numIpsUsed);
					for (int c =0; c < numHotspots; c++){
						if ((int)r==hotspots[c]) out=1;		// random came up with a hotspot, must redo
					}
				}
				get_bft_rel_addr((int)r);
				msgs[i].dest=tempAddr;

			}
		}

		else if (traffic==3) {	
			r = float_rand(1);
			if (numIps==64){
				if (r <= local){
					while (msgs[i].dest[0]== msgs[i].source[0])
						msgs[i].dest[0]=int_rand(4);
				}
				else if (r > local && r <= 1){
					msgs[i].dest[0]=int_rand(4);
					while (msgs[i].dest[2]== msgs[i].source[2] && msgs[i].dest[1]== msgs[i].source[1]){
						msgs[i].dest[2]=int_rand(4);
						msgs[i].dest[1]=int_rand(4);
					}
				}
			}
			else if (numIps==256){
				if (r <= local){
					while (msgs[i].dest[0]== msgs[i].source[0])
						msgs[i].dest[0]=int_rand(4);
				}
				else if (r > local && r <= 1){
					msgs[i].dest[0]=int_rand(4);
					while (msgs[i].dest[3]==msgs[i].source[3] && msgs[i].dest[2]== msgs[i].source[2] && msgs[i].dest[1]== msgs[i].source[1]){
						msgs[i].dest[3]=int_rand(4);
						msgs[i].dest[2]=int_rand(4);
						msgs[i].dest[1]=int_rand(4);
					}
				}


			}
			else cout << "\n traffic 3 error \n" << r;
		}
		else if (traffic==5 && a < 8) {
			r = float_rand(1);

			if (r <= 0.3){
				while (msgs[i].dest[0] + 4*msgs[i].dest[1] + 16*msgs[i].dest[2]==a){
					msgs[i].dest[1]=0;	// first ME Cluster
					msgs[i].dest[2]=0;
					msgs[i].dest[0]=int_rand(4);
				}
			}
			else if (r > 0.3 && r <= 0.6){
				while (msgs[i].dest[0] + 4*msgs[i].dest[1] + 16*msgs[i].dest[2]==a){
					msgs[i].dest[1]=1;	// second ME Cluster
					msgs[i].dest[2]=0;
					msgs[i].dest[0]=int_rand(4);
				}
			}
			else  if (r > 0.6 && r <= 0.733){
				while (msgs[i].dest[0] + 4*msgs[i].dest[1] + 16*msgs[i].dest[2]==a){
					msgs[i].dest[1]=2;	// Performace Monitor Cluster
					msgs[i].dest[2]=0;
					msgs[i].dest[0]=int_rand(4);
				}
			}
			else  if (r > 0.733 && r <= 0.866){
				while (msgs[i].dest[0] + 4*msgs[i].dest[1] + 16*msgs[i].dest[2]==a){
					msgs[i].dest[1]=3;	// first Peripherals cluster
					msgs[i].dest[2]=0;
					msgs[i].dest[0]=int_rand(4);
				}
			}
			else {
				while (msgs[i].dest[0] + 4*msgs[i].dest[1] + 16*msgs[i].dest[2]==a){
					msgs[i].dest[1]=0;	// second Peripherals cluster
					msgs[i].dest[2]=1;
					msgs[i].dest[0]=int_rand(4);
				}
			}
		}
		else if (traffic==5 && a > 7){
			while (msgs[i].dest[0]==a%4 && msgs[i].dest[1]== (a%16)/4 && msgs[i].dest[2] == a/16){
				msgs[i].dest[0]=int_rand(4);	// randomly choose destination
				msgs[i].dest[1]=int_rand(4);
				msgs[i].dest[2]=int_rand(4);
			}

		}

	}	// end BFT

	// all msgs

	msgs[i].header_moved=false;
	msgs[i].header_done=false;
	if (top_type==TORUS || top_type==MESH){
		msgs[i].source[0]=a;
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//		add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;
		while (msgs[i].dest[0]==a){			
			msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
		}
	}

	if (top_type==CUBE || top_type == SUPERS)
	{
		int *addr;
		get_cube_rel_addr(a);
		addr = tempAddr;
		for (int c=0; c < dimensions; c++)
		{
			msgs[i].source[c]=addr[c];
			msgs[i].dest[c]=addr[c];
		}

		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].upper=1;
		msgs[i].end_time=-2;  //active
		//add_msg_to_list(msgIndex);
		if (traffic==0)
		{
			while (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source))
			{			

				if(load <= 1.0)
				{
					for (int e=0; e< dimensions;e++)
					{
						msgs[i].dest[e]=int_rand(cube_dimensions[e]);	// uniform traffic
					}
				}
				else
				{ //benchmark traffic
					//for (int e=0; e< dimensions;e++)
					//{
					//	msgs[i].dest[e]=int_rand(cube_dimensions[e]);	// uniform traffic
					//}
					double temporary_number = float_rand(benchmarkLoad[a]);
					for(int dest_count = 0; dest_count < MST_N; dest_count++)
					{
						temporary_number -= FijMATRIX[a][dest_count];
						if(temporary_number <= 0.0)
						{
							if(top_type == SUPERS)
							{
								msgs[i].dest[0] = dest_count;
							}
							else
							{
								get_cube_rel_addr(dest_count);

								for(int e = 0; e < dimensions; e++)
								{
									msgs[i].dest[e] = tempAddr[e];
								}
							}
							dest_count = MST_N;
						}
					}
				}
			}
		}
		// hotspot traffic
		else if (traffic==2)
		{
			int *hDest;
			hDest = (int*) calloc(dimensions,sizeof(int));
			r = float_rand(100);
			//if going to hotspot
			if (r<hotPercent) {
				int h = (int)(r/(hotPercent/numHotspots));	// number of specific hotspot
				if (hotspots[h] == msgs[i].source[0])
				{
					h++;
				}
				if (h == numHotspots)
				{
					h = 0;
				}
				get_cube_rel_addr(hotspots[h]);
				hDest = tempAddr;
				for (int c=0; c < dimensions; c++)
				{
					if (hDest[c] < 0)
					{
						hDest[c] = 0;
					}
					msgs[i].dest[c]=hDest[c];
				}
			}
			//if going to a non-hotspot
			else {
				int out = 1;
				while (out==1) {
					out = 0;
					r = float_rand(numIpsUsed);
					for (int c =0; c < numHotspots; c++)
					{
						if ((int) r==hotspots[c]) 
							out=1;		// random came up with a hotspot, must redo
						if ((int) r == msgs[i].source[0])
							out=1;
					}
				}
				get_cube_rel_addr((int)r);
				hDest = tempAddr;
				for (int c=0; c < dimensions; c++)
				{
					if (hDest[c] < 0)
					{
						hDest[c] = 0;
					}
					msgs[i].dest[c]=hDest[c];
				}
			}
		}
		else if (traffic==3) 
		{
			bool loop=true;
			r = float_rand(1);
			// if local
			if (r < local) {
				while (loop){
					loop = false;
					for (int c=0; c < dimensions; c++)
						msgs[i].dest[c]=int_rand(cube_dimensions[c]);
					if (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source))
						loop=true;
					if (WRAP){
						if (get_cube_dist_torus(msgs[i].dest,msgs[i].source)!=1) 
							loop=true;
					}
					else {
						if (get_cube_dist_mesh(msgs[i].dest,msgs[i].source)!=1) 
							loop=true;
					}
				}
			}
			else {
				while (loop){
					loop = false;
					for (int c=0; c < dimensions; c++)
						msgs[i].dest[c]=int_rand(cube_dimensions[c]);
					if (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source))
						loop=true;
					if (WRAP){
						if (get_cube_dist_torus(msgs[i].dest,msgs[i].source)==1) 
							loop=true;
					}
					else {
						if (get_cube_dist_mesh(msgs[i].dest,msgs[i].source)==1) 
							loop=true;
					}
				}
			}
		}
		else if (traffic==4)
		{
			r = float_rand(1);
			// if local
			if (r < local) {
				while (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source)){			
					n = int_rand(cube_dimensions[0]);
					msgs[i].dest[0]=n;	// Same Column
				}
			}
			else {
				while (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source)){	
					while (msgs[i].source[0] == msgs[i].dest[0]) { // Make sure in a different column
						for (int e=0; e< dimensions;e++)
							msgs[i].dest[e]=int_rand(cube_dimensions[e]);	// uniform traffic
					}
				}
			}
		}
		else if (traffic == 6) //FFT
		{
			int* fftDest;
			fftDest = (int*) calloc(dimensions, sizeof(int));
			r = float_rand(100);
			int fft_help = r/16;
			for(int xx = 0; xx < numIps; xx++)
			{
				if(FFTmatrix[msgs[i].source[0]][xx] != 0)
				{
					fft_help--;
				}
				if(fft_help <= 0)
				{
					get_cube_rel_addr(xx);
					fftDest = tempAddr;
					for (int c=0; c < dimensions; c++)
					{
						if (fftDest[c] < 0)
						{
							fftDest[c] = 0;
						}
						msgs[i].dest[c]=fftDest[c];
					}

				}
			}
		}
		else if (traffic == 5) //transpose
		{
			int out = 0;
			int t0 = 0;
			int t1 = 0;

			for (int c = 0; c < numTranspose; c++)
			{
				if ((msgs[i].source[0] == transpose[c][0]) || (msgs[i].source[0] == transpose[c][1])) 
					out=1;		// transpose!
				if (transpose[c][0] == r)
				{
					t0 = c;
					t1 = -1;
				}
				if (transpose[c][1] == r)
				{
					t1 = c;
					t0 = -1;
				}
			}

			if (!out) //not one of the transpose pairs
			{
				while (get_cube_address(msgs[i].dest)==get_cube_address(msgs[i].source))
				{
					for (int e=0; e< dimensions;e++)
						msgs[i].dest[e]=int_rand(cube_dimensions[e]);	// uniform traffic
				}
			}
			else //a transpose pair
			{
				int *tDest;
				tDest = (int*) calloc(dimensions, sizeof(int));
				r = float_rand(100);
				if (r < transPercent) //doing transpose
				{
					if (t0 == -1)
						r = transpose[t1][1];
					else if (t1 == -1)
						r = transpose[t0][0];

					get_cube_rel_addr((int)r);
					tDest = tempAddr;
					for (int c=0; c < dimensions; c++)
					{
						if (tDest[c] < 0)
						{
							tDest[c] = 0;
						}
						msgs[i].dest[c]=tDest[c];
					}

				}
				else //not doing transpose
				{
					out = 1;
					while (out)
					{
						out = 0;

						r = float_rand(numIpsUsed);
						for (int c =0; c < numTranspose; c++)
						{
							if ((int) r == transpose[c][0] || (int) r == transpose[c][1]) 
								out=1;		// random came up with a transpose, must redo
							if ((int) r == msgs[i].source[0])
								out=1; // came up with source
						}
					}

					get_cube_rel_addr((int)r);
					tDest = tempAddr;
					for (int c=0; c < dimensions; c++)
					{
						if (tDest[c] < 0)
						{
							tDest[c] = 0;
						}
						msgs[i].dest[c]=tDest[c];
					}

				}
			}
		}

	}
	if (top_type== CLUSTERED){

		///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

		//get_clustered_rel_addr(14);
		//cout << "Address = 14, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(15);
		//cout << "Address = 15, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(16);
		//cout << "Address = 16, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(17);
		//cout << "Address = 17, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(18);
		//cout << "Address = 18, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(52);
		//cout << "Address = 52, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;
		//get_clustered_rel_addr(95);
		//cout << "Address = 95, coords: [" << tempAddr[2] << "," << tempAddr[1] << "," << tempAddr[0] << "]" << endl;
		//cout << "Getting address again..." << get_clustered_address(tempAddr) << endl;

		///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

		int *addr;
		get_clustered_rel_addr(a);
		addr = tempAddr;
		for (int c=0; c <= dimensions; c++){
			msgs[i].source[c]=addr[c];
			msgs[i].dest[c]=addr[c];
		}

		//messagesFile << "src :" << msgs[i].source[0] << ", " << "src :" << msgs[i].source[1] << ", " << "src :" << msgs[i].source[2] << ", " << endl;

		msgs[i].path_length = 1;
		msgs[i].upper=1;
		msgs[i].end_time=-2;  //active
		//add_msg_to_list(msgIndex);
		if (traffic==0){
			while (get_clustered_address(msgs[i].dest)==get_clustered_address(msgs[i].source)){			
				for (int e=0; e< dimensions;e++) {
					msgs[i].dest[e] = int_rand(cube_dimensions[e]);
					if(e == (dimensions-1)) {
						n = int_rand(ip_per_switch);
						msgs[i].dest[e+1]=n;	// uniform traffic
						msgs[i].path[0] = a*numPorts;   // store starting port in path
					}
				}
			}
		}
		else if (traffic==3) {
			r = float_rand(1);
			if (r < local) {
				do {
					do {
						for (int e=0; e< dimensions;e++) {
							msgs[i].dest[e] = int_rand(cube_dimensions[e]);
							if(e == (dimensions-1)) {
								n = int_rand(ip_per_switch);
								msgs[i].dest[e+1]=n;	// uniform traffic
								msgs[i].path[0] = a*numPorts;   // store starting port in path
							}
						}
						//cout << "  Temp Dist:" << get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) << endl;
					}while(get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) > 1);
					//cout << "src :" << msgs[i].source[0] << ", " << msgs[i].source[1] << ", " << msgs[i].source[2] << ", " << endl;
					//cout << "dest:" << msgs[i].dest[0] << ", " << msgs[i].dest[1] << ", " << msgs[i].dest[2] << ", " << endl;
					//cout << "Dist:" << get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) << endl;
					//cout << "Addr: src: " << get_clustered_address(msgs[i].source) << ", dest: " << get_clustered_address(msgs[i].dest) << endl;
				}while (get_clustered_address(msgs[i].dest)==get_clustered_address(msgs[i].source));
			}
			else {
				while (get_clustered_address(msgs[i].dest)==get_clustered_address(msgs[i].source)){
					do {
						for (int e=0; e< dimensions;e++) {
							msgs[i].dest[e] = int_rand(cube_dimensions[e]);
							if(e == (dimensions-1)) {
								n = int_rand(ip_per_switch);
								msgs[i].dest[e+1]=n;	// uniform traffic
								msgs[i].path[0] = a*numPorts;   // store starting port in path
							}
						}
						//cout << "  Temp Dist:" << get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) << endl;
					} while(get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) <= 1);
					//cout << "src :" << msgs[i].source[0] << ", " << msgs[i].source[1] << ", " << msgs[i].source[2] << ", " << endl;
					//cout << "dest:" << msgs[i].dest[0] << ", " << msgs[i].dest[1] << ", " << msgs[i].dest[2] << ", " << endl;
					//cout << "Dist:" << get_clustered_dist_mesh(msgs[i].source, msgs[i].dest) << endl;
					//cout << "Addr: src: " << get_clustered_address(msgs[i].source) << ", dest: " << get_clustered_address(msgs[i].dest) << endl;
				}
			}
		}
		else if (traffic==4) {

			bool loop=true;
			r = float_rand(1);
			// if local
			if (r < local) {
				while (get_clustered_address(msgs[i].dest)==get_clustered_address(msgs[i].source)){			
					n = int_rand(ip_per_switch);
					msgs[i].dest[dimensions]=n;	// Same Column
					if(ip_per_switch == 2) {
						n = int_rand(cube_dimensions[0]);
						msgs[i].dest[0] = n;
					}
					msgs[i].path[0] = a*numPorts;   // store starting port in path
				}
			}
			else {
				do {
					for (int e=0; e< dimensions;e++) {
						msgs[i].dest[e] = int_rand(cube_dimensions[e]);
						if(e == (dimensions-1)) {
							n = int_rand(ip_per_switch);
							msgs[i].dest[e+1]=n;	// uniform traffic
							msgs[i].path[0] = a*numPorts;   // store starting port in path
						}
					}
				} while (msgs[i].dest[dimensions] == msgs[i].source[dimensions] ||
					ip_per_switch==2 && msgs[i].dest[0]==msgs[i].source[0]); // Make sure it's a different column
			}
		}
		//messagesFile << "src :" << msgs[i].dest[0] << ", " << "src :" << msgs[i].dest[1] << ", " << "src :" << msgs[i].dest[2] << ", " << endl;

		///////////
		// TODO:
		// ADD traffic==1,2,3
		//////////
	}
	if (top_type== STACKED){
		int *addr;
		get_stacked_rel_addr(a);
		addr = tempAddr;
		for (int c=0; c <= dimensions; c++){
			msgs[i].source[c]=addr[c];
			msgs[i].dest[c]=addr[c];
		}

		msgs[i].path_length = 1;
		msgs[i].upper=1;
		msgs[i].end_time=-2;  //active
		//add_msg_to_list(msgIndex);
		if (traffic==0){
			while (get_stacked_address(msgs[i].dest)==get_stacked_address(msgs[i].source)){			
				for (int e=0; e < dimensions;e++) {
					msgs[i].dest[e] = int_rand(cube_dimensions[e]);
					if(e == (dimensions-1)) {
						n = int_rand(num_layers);
						msgs[i].dest[e+1]=n;	// uniform traffic
						msgs[i].path[0] = a*numPorts;   // store starting port in path
					}
				}
			}
		}
		else if (traffic==3) {
			r = float_rand(1);
			if (r < local) {
				while (get_stacked_address(msgs[i].dest)==get_stacked_address(msgs[i].source)){
					while(get_stacked_dist_mesh(msgs[i].source, msgs[i].dest)!= 1) {
						for (int e=0; e< dimensions;e++) {
							msgs[i].dest[e] = int_rand(cube_dimensions[e]);
							if(e == (dimensions-1)) {
								n = int_rand(num_layers);
								msgs[i].dest[e+1]=n;	// uniform traffic
								msgs[i].path[0] = a*numPorts;   // store starting port in path
							}
						}
					}
				}
			}
			else {
				while (get_stacked_address(msgs[i].dest)==get_stacked_address(msgs[i].source)){
					while(get_stacked_dist_mesh(msgs[i].source, msgs[i].dest) <= 1) {
						for (int e=0; e< dimensions;e++) {
							msgs[i].dest[e] = int_rand(cube_dimensions[e]);
							if(e == (dimensions-1)) {
								n = int_rand(num_layers);
								msgs[i].dest[e+1]=n;	// uniform traffic
								msgs[i].path[0] = a*numPorts;   // store starting port in path
							}
						}
					}
				}
			}
		}
		else if (traffic==4) {

			bool loop=true;
			r = float_rand(1);
			// if local
			if (r < local) {
				while (get_stacked_address(msgs[i].dest)==get_stacked_address(msgs[i].source)){
					n = int_rand(num_layers);
					msgs[i].dest[dimensions]=n;	// Same Column
					msgs[i].path[0] = a*numPorts;   // store starting port in path
				}
			}
			else {
				while (get_stacked_address(msgs[i].dest)==get_stacked_address(msgs[i].source)){
					for (int e=0; e< dimensions;e++) {
						msgs[i].dest[e] = int_rand(cube_dimensions[e]);
						if(e == (dimensions-1)) {
							n = int_rand(num_layers);
							msgs[i].dest[e+1]=n;	// uniform traffic
							msgs[i].path[0] = a*numPorts;   // store starting port in path
						}
					}
				}
			}
		}
		///////////
		// TODO:
		// ADD traffic==1,2,3
		//////////
	}
	if (top_type==RING){
		msgs[i].source[0]=a;
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//	add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;
		while (msgs[i].dest[0]==a){			
			msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
		}
	}

	if (top_type==HBUS){
		msgs[i].source[0]=a;
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		msgs[i].dest[0]=a;
		if (traffic==0){
			while (msgs[i].dest[0]==a){			
				msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
			}
			if (a/ips_per_bus != msgs[i].dest[0]/ips_per_bus) far_bus_tot++;
			else local_bus_tot++;
		}
		else if (traffic==3) {
			r = float_rand(1);
			if (r < local){
				while (msgs[i].dest[0]==a || msgs[i].dest[0]/ips_per_bus != a/ips_per_bus)
					msgs[i].dest[0]=int_rand(numIps);
				local_bus_tot++;
			}
			else {
				while (msgs[i].dest[0]==a || msgs[i].dest[0]/ips_per_bus == a/ips_per_bus)
					msgs[i].dest[0]=int_rand(numIps);
				far_bus_tot++;
			}
		}
	}
	if (top_type==OCTO){
		msgs[i].source[0]=a;
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;
		while (msgs[i].dest[0]==a){			
			msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
		}
	}


	if (top_type==OCTO5){

		msgs[i].source[0]=a;
		msgs[i].source[1]= a/8;	// ring
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//	add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;

		while (msgs[i].dest[0]==a){			
			msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
			if (msgs[i].dest[0]==0 || msgs[i].dest[0]==8 ||msgs[i].dest[0]==16 ||msgs[i].dest[0]==24)
				msgs[i].dest[0]=a;	// reset for invalid destinations.
		}
		msgs[i].dest[1]=msgs[i].dest[0]/8;
	}
	if (top_type==OCTOM){

		msgs[i].source[0]=a;
		msgs[i].source[1]= a/8;	// ring
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//	add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;

		if (traffic==0){
			while (msgs[i].dest[0]==a){			
				msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
			}
			msgs[i].dest[1]=msgs[i].dest[0]/8;
		}
		else if (traffic==3) {
			r = float_rand(1);

			if (r <= local){
				while (msgs[i].dest[0]== msgs[i].source[0]){
					msgs[i].dest[0]=int_rand(numIps);
					msgs[i].dest[1]=msgs[i].dest[0]/8;
					if (msgs[i].dest[1]!=msgs[i].source[1]) 
						msgs[i].dest[0]=msgs[i].source[0];
				}
			}
			else if (r > local && r <= 1){
				msgs[i].dest[0]=int_rand(numIps);
				msgs[i].dest[1]=msgs[i].dest[0]/8;
				while (msgs[i].dest[1]== msgs[i].source[1]){
					msgs[i].dest[0]=int_rand(numIps);
					msgs[i].dest[1]=msgs[i].dest[0]/8;
				}
			}
		}

	}
	if (top_type==OCTOM3||top_type==OCTOM256){


		msgs[i].source[0]=a;
		msgs[i].source[1]= a/8;	 // ring
		msgs[i].source[2]= a/64; // ring
		msgs[i].path[0] = a*numPorts + inject_port;   // store starting port in path
		msgs[i].path_length = 1;
		msgs[i].end_time=-2;  //active
		//	add_msg_to_list(msgIndex);
		msgs[i].dest[0]=a;

		if (traffic == 0){
			while (msgs[i].dest[0]==a){			
				msgs[i].dest[0]=int_rand(numIps);	// uniform traffic
			}
			msgs[i].dest[1]=msgs[i].dest[0]/8;
			msgs[i].dest[2]=msgs[i].dest[0]/64;
		}
		else if (traffic==3) {
			r = float_rand(1);

			if (r <= local){
				while (msgs[i].dest[0]== msgs[i].source[0]){
					msgs[i].dest[0]=8*msgs[i].source[1] + int_rand(8);
					msgs[i].dest[1]=msgs[i].dest[0]/8;
					msgs[i].dest[2]=msgs[i].dest[0]/64;
				}
			}
			else if (r > local && r <=1){

				msgs[i].dest[1]=msgs[i].source[1];

				while (msgs[i].dest[1]== msgs[i].source[1]){
					msgs[i].dest[1]=int_rand((numIps/8));
					msgs[i].dest[0]=8*msgs[i].dest[1] + int_rand(8);
					msgs[i].dest[2]=msgs[i].dest[0]/64;
				}
			}
		}
	}
}	// end 	generate_source_and_dest funk


/*void process_trace_injections(){
// this is for testing

for (int b = 0; b < 3; b++){
if (ips[0].generate[b] == 0 && ports[0*numPorts + 4].o_buff[b]==0) {// if ip not generating, make a new message

ips[0].generate[b] = msgl-1;

ips[0].generate_msgs[b] = msgIndex;
ports[0*numPorts + inject_port].o_buff[b] = msgIndex + 2*maxMessage;   // place header flit in o_buff

msgs[msgIndex].path[0] = 0*numPorts + inject_port;   // store starting port in path
msgs[msgIndex].path_length = 1;
msgs[msgIndex].start_time = cycles;
msgs[msgIndex].end_time=-2;  //active
//		add_msg_to_list(msgIndex);

msgs[msgIndex].source[0]=0;
msgs[msgIndex].source[1]=0;
msgs[msgIndex].dest[0]=3;
msgs[msgIndex].dest[1]=3;

msgIndex++;	
}
else if (ips[0].generate[b] > 0 && (ports[0*numPorts + inject_port].o_buff[b]==0 || ports[0*numPorts +inject_port].o_buff[b] == -ips[0].generate_msgs[b])) { // ip is generating, o_buff is empty
ips[0].generate[b]--;
ports[0*numPorts + inject_port].o_buff[b]=ips[0].generate_msgs[b];
if (ips[0].generate[b]==0) {
ports[0*numPorts + inject_port].o_buff[b]=ips[0].generate_msgs[b] + maxMessage;	// tail flits in the range 1025-2048
ips[0].generate_msgs[b]=0;		// reset generating message
}
}
}
}*/

void process_consumptions(){
	int message;
	int type;
	int buff;
	int this_port;

	for (int a = 0; a < numIps; a++)
	{
		this_port = a*numPorts + inject_port;

		for (int b = 0 ; b < numVirts; b++)
		{
			type=-1;

			/*if ((ports[a*numPorts + 4].i_buff[b] == 0) && cycles > 50)  {
			cout << "empty ips input buffer.  ip: "  << a << " time : "<< cycles << endl;
			}*/

			// search for header flits, then data, then tail to keep order
			for (int w = 0; w < bufferDepth; w++)
			{
				if (ports[this_port].i_buff[b*bufferDepth+w] >2*maxMessage){	// header flit found
					type = 0;
					buff = b*bufferDepth+w;
					w = bufferDepth +10;  // to exit loop
				}
			}
			if (type==-1)
			{
				for (int z = 0; z < bufferDepth; z++)
				{
					if (ports[this_port].i_buff[b*bufferDepth+z]>0 && ports[this_port].i_buff[b*bufferDepth+z]<maxMessage){	// data flit found
						type = 1;	// data
						buff = b*bufferDepth+z;
						z = bufferDepth +10;  // to exit loop
					}
				}
			}
			if (type==-1)
			{
				for (int y = 0; y < bufferDepth; y++)
				{
					if (ports[this_port].i_buff[b*bufferDepth+y]>maxMessage){	// tail flit found
						type = 2; // tail
						buff = b*bufferDepth+y;
						y = bufferDepth +10;  // to exit loop
					}
				}
			}

			if (type!=-1) {	// need to consume a flit
				message = ports[this_port].i_buff[buff]%maxMessage;
				if (type==0) {// if it's a header flit
					// find an empty consuming bin
					/*if(msgs[message].wait == -1)
					{
						int total_repeaters = 0;
						if(fALASH || fLASH)
						{
							for(int i =0 ; i < msgs[message].path_length-1; i++)
							{
								total_repeaters += numRepeaters[msgs[message].path[i]/numPorts][msgs[message].path[i+1]/numPorts];
							}
						}
						msgs[message].wait = total_repeaters;
						msgs[message].header_done=true;

					}
					if(msgs[message].wait > 0)
					{
						msgs[message].wait--;
					}
					else if(msgs[message].wait == 0)
					{*/
						for (int c = 0; c < numVirts; c++)
						{
							if (ips[a].consume_msgs[c]==0) 
							{
								ips[a].consume[c]=msgl-1;				 // start the consume countdown
								ips[a].consume_msgs[c]=message;		// store message that's being consumed
								ports[this_port].i_buff[buff] = -message;	// leave token for following data flits
								msgs[message].header_done=true;
								c = numVirts + 1;								// exit loop
							}
						}
					//}
					//ports[a*numPorts + 4].i_buff[buff] = 0;
				}
				else {						// it's a data flit
					// find its appopriate bin
					for (int d = 0; d < numVirts; d++)
					{
						if (ips[a].consume_msgs[d]==message)
						{
							ips[a].consume[d]--;
							ports[this_port].i_buff[buff] = -message;	// leave token
							if (ips[a].consume[d]==0) {
								messageTotal[msgs[message].sourceOrig][msgs[message].dest[0]]++;
								latencyPairs[msgs[message].sourceOrig][msgs[message].dest[0]] += msgs[message].end_network - msgs[message].start_network;
								if (DUMP)	messagesFile << "MSG: " << message << " completed at time: " << cycles << " Latency: " << cycles-msgs[message].start_time << endl;
								//if (DUMP && cycles - msgs[message].start_time > 500) cout << "MSG: " << message << " completed at time: " << cycles << " Latency: " << cycles-msgs[message].start_time << endl;
								temp_done++;
								msgs[message].end_time = cycles;
								////////////////////////////////////////////////////////////////////////////////////////////////////////////////
								int supercycles = 0;
								int scount = 0;
								int v;
								int w;

								network_latency = network_latency + msgs[message].end_network - msgs[message].start_network;
								total_latency = total_latency + cycles - msgs[message].start_time;
								
							//	if((msgs[message].end_network - msgs[message].start_network) > 500)
									//cout << "Check" << endl;
								//if((cycles - msgs[message].start_time) > 1000)
									//cout << "Check" << endl;
								if(top_type == SUPERS && connection_type == 5)
								{
									for(scount = 0; scount < (msgs[message].path_length - 1); scount++)
									{
										v = msgs[message].path[scount];
										w = msgs[message].path[scount+1];

										v %= numPorts;
										w %= numPorts;
										//	supercycles += lookupcycle[v][w];
									}
								}

								//	total_latency += supercycles;

								if (select_function==3){
									if (msgs[message].priority==0) {
										total_latency0 = total_latency0 + cycles - msgs[message].start_time;
										total_latency0 += supercycles;
										messages_done0++;
									}
									if (msgs[message].priority==1) {
										total_latency1 = total_latency1 + cycles - msgs[message].start_time;
										total_latency1 += supercycles;
										messages_done1++;
									}
									if (msgs[message].priority==2) {
										total_latency2 = total_latency2 + cycles - msgs[message].start_time;
										total_latency2 += supercycles;
										messages_done2++;
									}
									if (msgs[message].priority==3) {
										total_latency3 = total_latency3 + cycles - msgs[message].start_time;
										total_latency3 += supercycles;
										messages_done3++;
									}
								}
								temp_lat = temp_lat + cycles - msgs[message].start_time;
								temp_lat += supercycles;
								messages_done++;
								if(msgs[message].wireless)
									wireless_done++;
								
								//messageDump << "Message " << message << ": Start: " << msgs[message].start_time << " End: " << msgs[message].end_time << endl;
								//messageDump << msgs[message].source[0] << "-->" << msgs[message].dest[0] << endl;

								for(int path_counter = 2; path_counter < msgs[message].path_length-2; path_counter+=2)
								{
									int lowerVfi = (vfiClustering[clusterMatrix[msgs[message].path[path_counter]/numPorts-NUM_IPS]] < vfiClustering[clusterMatrix[msgs[message].path[path_counter+1]/numPorts-NUM_IPS]]) ? clusterMatrix[msgs[message].path[path_counter]/numPorts-NUM_IPS] : clusterMatrix[msgs[message].path[path_counter+1]/numPorts-NUM_IPS];
									if(path_counter != 2)
									{
										
										messageVfiTotal[msgs[message].sourceOrig][msgs[message].dest[0]][clusterMatrix[msgs[message].path[path_counter]/numPorts-NUM_IPS]] += 64;
									}
									if(!fMESH)
										messageVfiTotal[msgs[message].sourceOrig][msgs[message].dest[0]][lowerVfi] += (numRepeaters[msgs[message].path[path_counter]/numPorts][msgs[message].path[path_counter+1]/numPorts]+1) * 64;
								}
								for(int path_counter = 0; path_counter < msgs[message].path_length; path_counter++)
								{
									link_flit_counter[msgs[message].path[path_counter]]++;
									node_flit_counter[(msgs[message].path[path_counter]/numPorts)]++;
									RT[(msgs[message].path[path_counter]/numPorts)].commDensity += 1.0;
									//messageDump << msgs[message].path[path_counter] << "->";
								}
								//flitsPerLink[msgs[message].source[0]][msgs[message].source[0]] += 64;
								//flitsPerLink[msgs[message].dest[0]][msgs[message].dest[0]] += 64;
								if(fALASH)
								{
									for(int path_counter = 2; path_counter < msgs[message].path_length-3; path_counter += 2)
									{
										//if(connections[msgs[message].path[path_counter]/numPorts][msgs[message].path[path_counter+1]/numPorts][0] == 'D')
										//	flitsPerLink[msgs[message].path[path_counter]/numPorts-numIps][msgs[message].path[path_counter+1]/numPorts-numIps] += 64;
										//else
										//	wirelessUsage[msgs[message].path[path_counter]/numPorts-numIps] += 64;
									}
									for(int path_counter = 0; path_counter < msgs[message].path_length - 1; path_counter += 2)
									{
										communication_density[msgs[message].path[path_counter]/numPorts][msgs[message].path[path_counter+1]/numPorts][msgs[message].vpath[path_counter]] += 1.0;
									}
								}
								else
								{
									for(int path_counter = 2; path_counter < msgs[message].path_length-3; path_counter += 2)
									{
									//		flitsPerLink[msgs[message].path[path_counter]/numPorts-numIps][msgs[message].path[path_counter+1]/numPorts-numIps] += 64;
									}
								}
								//messageDump << endl;
								flit_hop_count += msgs[message].path_length;
								total_flit_count++;

								remove_msg_from_list(message);
								ips[a].consume_msgs[d]=0;		// reset message being consumed
								for(int i = 0; i < bufferDepth; i++)
								{
									ports[this_port].i_buff[b*bufferDepth+i] = 0;
								}

								if (cycles - msgs[message].start_time < maxLatency && cycles>reset)	// for debugging
									latency_histogram[cycles - msgs[message].start_time]++;
							}
						}
					}

				}
			}	
		}
	}
}

int find_level_bft(int nd){
	int a=numNodes;
	for (int b = levels; b >0; b--){
		a = a - numIps/((int)pow((float) 2,(float)(b+1)));  //(6/1 Kevin: change pow(2,(float)(b+1)) to pow((float) 2,(float)(b+1)))
		if (nd>=a) return b;
	}
	return -1;
}
int find_level_kary(int nd){
	int a=numNodes;
	for (int b = levels; b >0; b--){
		a = a - numSwitches/levels;
		if (nd>=a) return b;
	}
	return -1;
}

// takes message m ,  returns target port 
int route_octom(int m){ 
	int ring;
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;
	ring = (int) (nd-numIps)/8;
	// if destination is in local ring
	if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1] == ring){
		// if destination reached
		if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0] == nd-numIps)
			port= nd*numPorts;
		// if straight across
		else if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0] == (nd-numIps+4)%8 + ring*8)
			port = nd*numPorts+3;	
		else if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0] == (nd-numIps+1)%8 + ring*8 ||
			msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0] == (nd-numIps+2)%8  + ring*8 ||
			msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0] == (nd-3)%8  + ring*8)
			port= nd*numPorts +2;	// go up in number
		else
			port = nd*numPorts +1;	// go down in number
		if (octoTraffic==1){	// avoid using 0-7, 7-0 links
			if (nd==7 && port==nd*numPorts+2) 
				port = nd*numPorts+1;	// go down to 6 instead
			if (nd==6 && msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0]==0) 
				port = nd*numPorts+1;	// go down to 5 instead
			if (nd==0 && port==nd*numPorts+1) 
				port = nd*numPorts+2;	// go up to 1 instead
			if (nd==1 && msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[0]==7) 
				port = nd*numPorts+2;	// go up to 2 instead
		}
	}
	// need to move to appropriate ring
	else{
		if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1] == (ring+1)%8 ||
			msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1] == (ring+2)%8 ||
			msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1] == (ring+5)%8)
			port = nd*numPorts + 5;
		else if (msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1] == (ring+4)%8)
			port = nd*numPorts + 6;
		else 
			port = nd*numPorts + 4;

		if (octoTraffic==1){ 
			if (ring==7 && port==nd*numPorts+5) 
				port = nd*numPorts+4;	// go down to 6 instead
			if (ring==6 && msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1]==0) 
				port = nd*numPorts+4;	// go down to 5 instead
			if (ring==0 && port==nd*numPorts+4) 
				port = nd*numPorts+5;	// go up to 1 instead
			if (ring==1 && msgs[ports[pt].i_buff[buff] % (2*maxMessage)].dest[1]==7) 
				port = nd*numPorts+5;	// go up to 2 instead
		}
	}

	return (port);
}

int route_octom256(int m){
	int ring_of_8, ring_of_64;
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;


	ring_of_8 = (int) (nd-numIps)/8;
	ring_of_64 = (int) (nd-numIps)/64;

	// if destination is in local ring
	if (msgs[m].dest[1] == ring_of_8){
		// if destination reached
		if (msgs[m].dest[0] == nd-numIps)
			port= nd*numPorts;
		// if straight across
		else if (msgs[m].dest[0] == (nd+4)%8 + ring_of_8*8)
			port = nd*numPorts+3;	
		else if (msgs[m].dest[0] == (nd+1)%8 + ring_of_8*8 ||
			msgs[m].dest[0] == (nd+2)%8  + ring_of_8*8 ||
			msgs[m].dest[0] == (nd-3)%8  + ring_of_8*8)
			port= nd*numPorts +2;	// go up in number
		else
			port = nd*numPorts +1;	// go down in number
	}
	// need to move to appropriate ring_of_8, it's in the right 64 IP ring
	else if (msgs[m].dest[2] == ring_of_64) {
		if (msgs[m].dest[1] == (ring_of_8+1)%8 + ring_of_64*8 ||
			msgs[m].dest[1] == (ring_of_8+2)%8 + ring_of_64*8 ||
			msgs[m].dest[1] == (ring_of_8+5)%8 + ring_of_64*8)
			port = nd*numPorts + 5;
		else if (msgs[m].dest[1] == (ring_of_8+4)%8 + ring_of_64*8)
			port = nd*numPorts + 6;
		else 
			port = nd*numPorts + 4;
		if (octoTraffic!=0){
			// correct to eliminate cycles
			if (ring_of_8==7 && port == nd*numPorts+5)
				port = nd*numPorts+4;
			if (ring_of_8==6 && msgs[m].dest[1] ==0)
				port = nd*numPorts+4;
			if (ring_of_8==0 && port == nd*numPorts+4)
				port = nd*numPorts+5;
			if (ring_of_8==1 && msgs[m].dest[1] ==7)
				port = nd*numPorts+5;
		}
	}
	// need to move to appropriate ring_of_64
	else {
		if (msgs[m].dest[2] == (ring_of_64+1)%4)
			port = nd*numPorts + 8;
		else if (msgs[m].dest[2] == (ring_of_64+2)%4)
			port = nd*numPorts + 9;
		else 
			port = nd*numPorts + 7;
		if (octoTraffic!=0){
			// correct to eliminate cycles
			if (ring_of_64==3 && port == nd*numPorts+8)
				port = nd*numPorts+7;
			if (ring_of_64==0 && port == nd*numPorts+7)
				port = nd*numPorts+8;
		}
	}
	return (port);
}

int route_from_child(int node, int m, int l){
	int p;
	bool turnaround = true;


	if (numNodes==376 || numNodes==1520){
		for (int z = levels-1; z >= l; z--){
			if (msgs[m].dest[z]!=msgs[m].source[z])
				turnaround=false;
		}
	}
	else {
		for (int z = levels-1; z >= l; z--){
			if (msgs[m].dest[z]!=msgs[m].source[z])
				turnaround=false;
		}
	}	

	if (turnaround==false) { // send up tree via random empty parent link


		if (numPorts ==6) {
			p = int_rand(2) + 4;			// randomly choosed p0 or p1 link, (p=4 or 5)	
			// first check for tokens, real or -ve
			for (int a = 0; a < numVirts; a++){
				for (int q=0; q < bufferDepth; q++)
					if (ports[node*numPorts + p].o_buff[a*bufferDepth+q]%maxMessage == -m || ports[node*numPorts + p].o_buff[a*bufferDepth+q]%maxMessage == m)
						return p;
			}
			if (p==4) p=5;
			else if (p==5) p=4;
			// check for tokens at other port. real or -ve
			for (int b = 0; b < numVirts; b++){
				for (int r=0; r < bufferDepth; r++)
					if (ports[node*numPorts + p].o_buff[b*bufferDepth+r]%maxMessage == -m || ports[node*numPorts + p].o_buff[b*bufferDepth+r]%maxMessage == -m)
						return p;				
			}


			for (int y = 0; y < 2; y++)
				free_lanes[y]=0;		// initailize array

			p = 4;

			for (int c = 0; c < numVirts; c++){
				int z;
				// find the parent port with the most completely empty buffers
				for (z = 0; z < bufferDepth; z++)
					if (ports[node*numPorts + p].o_buff[c*bufferDepth+z] != 0)
						z = bufferDepth+10;
				if (z==bufferDepth) // if this is true, all buffers are free in this lane
					free_lanes[p-4]++;
			}

			p = 5;

			for (int c = 0; c < numVirts; c++){
				int y;
				// find the parent port with the most empty buffers
				for (y = 0; y < bufferDepth; y++)
					if (ports[node*numPorts + p].o_buff[c*bufferDepth+y] != 0)
						y = bufferDepth+10;
				if (y==bufferDepth) // if this is true, all buffers are free in this lane
					free_lanes[p-4]++;
			}
			// search for emptiest parent port, and return it
			if (free_lanes[0]>free_lanes[1]) 
				return 4;
			else
				return 5;	// return other port even if it's full
		}

		if (numPorts ==8){

			p = int_rand(4) + 4;			// randomly choosed p0,p1,p2,or p3 link, (p=4..7)	
			// first check for tokens, real or -ve
			for (int pc=0; pc < 4; pc++){
				for (int a = 0; a < numVirts; a++){
					for (int q=0; q < bufferDepth; q++)
						if (ports[node*numPorts + p].o_buff[a*bufferDepth+q]%maxMessage == -m || ports[node*numPorts + p].o_buff[a*bufferDepth+q]%maxMessage == m)
							return p;
				}
				p++;
				if (p==8) p=4;
			}		
			// check for tokens at other port. real or -ve
			for (int pc=0; pc < 4; pc++){
				for (int b = 0; b < numVirts; b++){
					for (int r=0; r < bufferDepth; r++)
						if (ports[node*numPorts + p].o_buff[b*bufferDepth+r]%maxMessage == -m || ports[node*numPorts + p].o_buff[b*bufferDepth+r]%maxMessage == -m)
							return p;				
				}
				p++;
				if (p==8) p=4;
			}


			for (int y = 0; y < 4; y++)
				free_lanes[y]=0;		// initailize array

			p = 4;

			for (int pc =0; pc < 4; pc++){
				for (int c = 0; c < numVirts; c++){
					int z;					
					// find the parent port with the most completely empty buffers
					for (z = 0; z < bufferDepth; z++)
						if (ports[node*numPorts + p].o_buff[c*bufferDepth+z] != 0)
							z = bufferDepth+10;
					if (z==bufferDepth) // if this is true, all buffers are free in this lane
						free_lanes[p-4]++;
				}
				p++;
				if (p==8) p=4;
			}

			int high_index = 0;
			int high_value = 0;
			// search for emptiest parent port, and return it
			for (int pc=0; pc<4; pc++){
				if (free_lanes[pc]>high_value) {
					high_index=pc;
					high_value=free_lanes[pc];
				}					
			}

			return high_index+4;
		}
	}
	else {	// turnaround to appropriate child port
		return msgs[m].dest[l-1];
	}
}

int find_oldest(int node, int start_port, int stop_port){
	int oldest_port=0;
	int oldest_start_time=DUR+2;
	int m;
	for (int a = start_port; a <= stop_port; a++){
		for (int b = 0; b < numVirts; b++){
			for (int c = 0; c < bufferDepth; c++){
				// if it's a header
				if (ports[node*numPorts+a].i_buff[b*bufferDepth+c]>2*maxMessage) {
					m = ports[node*numPorts+a].i_buff[b*bufferDepth+c]%maxMessage;
					// if it's older
					if (msgs[m].start_time<oldest_start_time){
						oldest_start_time= msgs[m].start_time;
						oldest_port=a;
					}
				}
			}
		}		
	}
	return oldest_port;
}

int max (int x, int y){
	if (x > y) return x;
	else return y;
}

int mypow(int x, int pow)
{
	int n=1;
	for(int i=0; i < pow; i++)
		n *= x;
	return n;
}

void add_msg_to_list(int i){

	if (firstMsg==-1) { // message list is empty
		firstMsg=i;
		msgs[i].prev = -1;
		msgs[i].next = -1;
		currentMsg = firstMsg;
	}
	else {
		msgs[i].prev=currentMsg;
		msgs[currentMsg].next=i;
		currentMsg=i;
		msgs[i].next=-1;
	}
	msgs[i].num=i;
	numActiveMsgs++;
}

void remove_msg_from_list(int i){	

	if (numActiveMsgs==1){  // this is the last active message
		currentMsg=-1;
		firstMsg=-1;
	}
	else{
		if (currentMsg==i){ //if end of the line, move current back
			currentMsg=msgs[i].prev;
			msgs[currentMsg].next=-1;
		}
		else if (i==firstMsg) { // it's the first in line
			firstMsg=msgs[i].next;
			if (msgs[i].next!=-1) msgs[msgs[i].next].prev=-1;
		}
		else {	// if it's somewhere in the middle
			msgs[msgs[i].prev].next = msgs[i].next;
			if (msgs[i].next!=-1) msgs[msgs[i].next].prev=msgs[i].prev;
		}
	}
	numActiveMsgs--;
}

// for debugging, prints msg nums of active msgs
void print_active_msgs(){

	int nextMsg = firstMsg;


	for (int a=0; a < numActiveMsgs; a++){
		cout << " " << nextMsg;
		nextMsg = msgs[nextMsg].next;
	}
	cout << endl;
}



int calc_active_msgs(){
	int sum = 0;
	// search through msgs, to find number with an active start time, but no stop time (-1)
	for (int a = 0; a < maxMessage; a++){
		if (msgs[a].end_time==-2) sum++;
	}
	return sum;

}

void do_avg_queue_calc(){

	for (int a=0; a < numIps; a++){
		avg_queue_size=avg_queue_size+ips[a].queue_pop;
		temp_avg_queue_size=temp_avg_queue_size+ips[a].queue_pop;
	}
}

void clear_res_tokens(){
	for (int a=0; a < total_num_of_ports; a++){
		for (int b = 0; b < numVirts*bufferDepth; b++){
			if (ports[a].i_buff[b]==RES_TOKEN2) ports[a].i_buff[b]=0;
			if (ports[a].o_buff[b]==RES_TOKEN2) ports[a].o_buff[b]=0;
			if (ports[a].i_buff[b]==RES_TOKEN1) ports[a].i_buff[b]=RES_TOKEN2;
			if (ports[a].o_buff[b]==RES_TOKEN1) ports[a].o_buff[b]=RES_TOKEN2;

		}
	}

}

void update_bus_network(){

	process_consumptions();
	//circuit_switch_bus();
	set_bus_moves();
	process_injections();
	if (PORTSDUMP) printBus();
}

void update_network(){


	int old_moves=0;
	for (int g = 0; g < maxMessage; g++){
		msgs[g].header_moved=false;
		msgs[g].is_blocked=false;
		msgs[g].temp_priority=-1;
		msgs[g].req_port=-1;
	}
	bool go = true;
	if (GHOST) clear_res_tokens();
	
	for(int i = 0 ; i < maxMessage; i++)
	{
		if(msgs[i].end_network == -1 && msgs[i].header_done)
		{
			bool tailDone = false;

			for(int j = 0; j < numVirts*bufferDepth; j++)
			{
				if(ports[msgs[i].path[msgs[i].path_length-3]].i_buff[j] == i+maxMessage)
				{
					tailDone = true;
				}
			}
			if(tailDone)
				msgs[i].end_network = cycles;
		}
	}
	
	process_consumptions();

	if(fDVFS)
	{
		for(int i = 0; i < numNodes; i++)
		{
			for(int j = i; j < numNodes; j++)
			{
				if(linkNums[i][j] > 0 && linkNums[i][j] < 124)
				{
					int port1 = connection[i][j];
					int port2 = connection[j][i];
					bool empty = true;
					for(int k = 0; k < (bufferDepth*numVirts); k++)
					{
						if(ports[port1].o_buff[k] > 0 || ports[port2].o_buff[k] > 0)
						{
							empty = false;
							break;
						}
					}
					if(!empty)
					{
						dvfsOutput << cycles << "\tf\t" << linkNums[i][j]  <<  endl;
					}
				}
			}
		}
	}
	if(cycles %50 == 0 && fDVFS)
	{
		double best_commDens = 100000;
		double commDens = 0;
		int bestLayer = -1;
		int bestPath = -1;
		int next_switch = -1;

		for(int source = 0; source < numIps; source++)
		{
			for(int dest = 0; dest < numIps; dest++)
			{
				if(source != dest)
				{
					best_commDens = 100000;
					bestPath = -1;
					next_switch = -1;
					for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
					{
						if( MultiPathLength[source][dest][pathnumber] > 0)
						{
							for(int j = numLayers-1; j >= 0 ; j--)
							{
								commDens = 0;
								if(pathAllocLayer[source][dest][pathnumber][j] == 1)
								{
									for (int i = 1; i < MultiPathLength[source][dest][pathnumber]-2; i++)
									{
										commDens += communication_density[MultiPathMsg[source][dest][pathnumber][i]][MultiPathMsg[source][dest][pathnumber][i+1]][j];
									}
									if(commDens < best_commDens)
									{
										best_commDens = commDens;
										bestPath = pathnumber;
									}
								}
							}
						}
					}
					next_switch = MultiPathMsg[source][dest][bestPath][2];
					if(connections[source+numIps][next_switch][0] != 'D')
					{
						bool rerout = false;
						switch(connections[source+numIps][next_switch][0])
						{
						case '1':
							if(token1 != (source+numIps))
								rerout = true;
							break;
						case '2':
							if(token2 != (source+numIps))
								rerout = true;
							break;
						case '3':
							if(token3 != (source+numIps))
								rerout = true;
							break;
						default:
							cout << "Shouldn't Get Here" << endl;
						}
						if(fDVFS)
						{
							if(!rerout)
								currentDecision << cycles << "\t" << source << "\t" << dest << "\t" << linkNums[source+numIps][next_switch] << endl;
						}
						best_commDens = 100000;
						bestPath = -1;
						next_switch = -1;
						for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
						{
							if( MultiPathLength[source][dest][pathnumber] > 0 && pathnumber != wirelessPathNum)
							{
								for(int j = numLayers-1; j >= 0 ; j--)
								{
									commDens = 0;
									if(pathAllocLayer[source][dest][pathnumber][j] == 1 && pathnumber != wirelessPathNum)
									{
										for (int i = 1; i < MultiPathLength[source][dest][pathnumber]-2; i++)
										{
											commDens += communication_density[MultiPathMsg[source][dest][pathnumber][i]][MultiPathMsg[source][dest][pathnumber][i+1]][j];
										}
										if(commDens < best_commDens)
										{
											best_commDens = commDens;
											bestPath = pathnumber;
										}
									}
								}
							}
						}
						next_switch = MultiPathMsg[source][dest][bestPath][2];
						if(bestPath == wirelessPathNum || bestPath == -1)
							cout << "Something Went Wrong" << endl;
						if(fDVFS)
							currentDecision << cycles << "\t" << source << "\t" << dest << "\t" << linkNums[source+numIps][next_switch] << endl;
					}
					else
					{
						if(fDVFS)
							currentDecision << cycles << "\t" << source << "\t" << dest << "\t" << linkNums[source+numIps][next_switch] << endl;
					}
				}
			}
		}

		for(int source = numIps; source < numNodes; source++)
		{
			for(int dest = source; dest < numNodes; dest++)
			{
				if(source != dest)
				{
					int count = 0;
					int port = 0;
					if(connection[source][dest] != -1 && connections[source][dest][0] == 'D')
					{
						port = connection[source][dest];
						for(int i = 0; i < numVirts; i++)
						{
							for(int j = 0; j < bufferDepth; j++)
							{
								if(ports[port].o_buff[i*bufferDepth+j] != 0)
								{
									count++;
									break;
								}
							}
						}
						port = connection[dest][source];
						for(int i = 0; i < numVirts; i++)
						{
							for(int j = 0; j < bufferDepth; j++)
							{
								if(ports[port].o_buff[i*bufferDepth+j] != 0)
								{
									count++;
									break;
								}
							}
						}
						if(fDVFS)
							openVirts << cycles << "\t" <<   linkNums[source][dest] << "\t" << count << endl;
					}
				}
			}
		}
	}
	

	while (go==true){
		counter++;
		set_internode_moves(0,numNodes-1,0,numPorts-1);
		set_intranode_moves(numIps,numNodes-1,0,numPorts-1);
		detect_collisions();
		if (select_function==3) detect_blocking();

		if (old_moves==intranode_moves+internode_moves) // no movement
			go = false;	// quit loop
		old_moves=intranode_moves+internode_moves;
		//cout << counter << " " << old_moves << endl;
		if (RUNONCE) go = false;	// run once only
	}

	// process_trace_injections adds to the queues
	if (USETRACE) process_trace_injections();
	process_injections();

	process_internode_moves();	// actually advance flits along links.	
	process_intranode_moves();	// actually advance flits in switches.	

	//for(int i = 0; i < maxMessage; i++)
	//{
	//	if(msgs[i].header_done == false &&(cycles - msgs[i].start_time) > 200 && msgs[i].end_time == -2)
	//	{
	//		cout << "Really Long Time " << i << endl;
	//	}
	//}

	for(int i = 1; i < maxMessage; i++)
	{
		if(msgs[i].wait > 0)
			msgs[i].wait--;
		else if(msgs[i].wait == 0)
			msgs[i].wait = -1;
	}

	for(int i = 1; i < maxMessage; i++)
	{
		if(msgs[i].end_time == -2)
		{
			if(msgs[i].path_length == 3 && msgs[i].start_network == -1)
			{
				msgs[i].start_network = cycles;
			}
			
		}
	}

	int b =0;
	int port_limit;
	if (top_type==OCTO5) port_limit = 300;
	else port_limit = numPorts*numNodes;
	for (int a = 0; a < port_limit; a++){
		if (ports[a].sent_this_cycle) b++;
		/*else{

		if ((a  > numIps*numPorts) || ((a - 4)%numPorts==0))
		if (a <20*numPorts)pr
		linkuseFile << "Time: " << cycles << " Port: " << a << " not used.  i_buffs: " << ports[ports[a].next].i_buff[0] << endl; //" " << ports[ports[a].next].i_buff[1] << endl;
		else
		if (a%numPorts<4)
		linkuseFile << "Time: " << cycles << " Port: " << a << " not used.  i_buffs: " << ports[ports[a].next].i_buff[0] << endl; //" " << ports[ports[a].next].i_buff[1] << endl;
		}*/
		ports[a].sent_this_cycle=false;
		ports[a].sent_this_cycle_intra=false;
	}
	//cout << cycles << " cycles \t" << b << " link moves\n";
	if (AVGQ) do_avg_queue_calc();
	if (ACTMSGS) activeMessages = activeMessages + calc_active_msgs();
	if (PORTSDUMP) dump_ports();
	if (GATEDUMP) dump_gateways();
	//if (cycles>22500) { DUMP=true; PORTSDUMP=true; }
	//print_active_msgs();
} 

float find_largest_param(){
	float maxParam = 0;
	for (int a = 0; a < runs; a++)
		if (vary[a]>maxParam) maxParam=vary[a];
	return maxParam;

}
/* set parameters to default values*/
void setDefaults(){

	runs=1;
	varyParam=0;
	vary = (float*) calloc (100, sizeof(float)); // max intervals is 100
	top_type=BFT;
	numPorts=6;
	inject_port=4;
	numIps=64;
	numIpsUsed=numIps;
	levels= (int)ceil(log((double)numIps)/log((double)4)); 
	numSwitches=0;
	for (int a=1; a<=levels; a++)
		numSwitches=numSwitches+numIps/((int)pow((float)2,a+1));
	numNodes=numIps+numSwitches;
	bufferDepth=2;
	numVirts=4;
	queueSize=100;
	DUR=1000000;		// yuchen: the higher, the more accurate
	reset=2000;
	step=1000;
	traffic=0;
	msgl=64;
	load=1.0;
	local=0;
	//step=10000;
	DUMP=true;
	PORTSDUMP=0;
	PRINTADJ=0;
	AVGQ=1;
	SAT=1;
	GHOST=0;
	WRAP=1;
	RES_TOKEN1=-2*maxMessage;
	RES_TOKEN2=-3*maxMessage;
	ACTMSGS=0;
	select_function=0;
	RUNONCE=true;
	USETRACE=false;
	a_on  = 1.9;        // For self-similar traffic
	a_off = 1.25;       // For self-similar traffic

	/*	top_type=HBUS;
	numPorts=1;
	numIps=64;
	numIpsUsed=64;
	ips_per_bus=numIps/4;
	inject_port=0;
	numNodes=64;*/
}

/* display all network parameters on the screen*/
void printParameters(){
	int a;
	cout << "* * * * * * * * * * * * * * * * * * * * * * * * * * * * *\n";
	cout << "CURRENT NETWORK/TRAFFIC PARAMETERS\n";
	switch(top_type){
	case(HBUS): cout << "1 - 4x-Bus\n"; break;
	case(BFT): cout << "1 - Butterfly Fat Tree\n"; break;
	case(RING): cout << "1 - Ring\n"; break;
	case(KARY): cout << "1 - K-ary N-Tree\n"; break;
	case(MESH): cout << "1 - K-ary N-Cube (mesh)\n"; break;
	case(TORUS): cout << "1 - K-ary N-Cube (toriod)\n"; break;
	case(OCTO): cout << "1 - Octagon\n"; break;
	case(CUBE): if (WRAP) cout << "1 - K-ary N-Cube (torus)\n"; 
				else cout << "1 - K-ary N-Cube (mesh)\n"; 	break;
	case(CLUSTERED): cout << "1 - Clustered" << endl; break;
	case(STACKED): cout << "1 - Stacked Mesh" << endl; break;
	case(SUPERS): cout << "1 - SUPER --" << numPorts << "--" << endl; break;
	}
	cout << "2 - Number of IPs: " << numIpsUsed << endl;
	cout << "3 - Buffer Depth (flits): " << bufferDepth 
		<< "\n4 - Virtual Channels: " << numVirts
		<< "\n5 - Source Queue Length (messages): " << queueSize << endl;
	cout << "6 - Simulation Duration (cycles): " << DUR << "\n7 - Reset stats at time: " << reset << endl;
	cout << "8 - Traffic Type: ";
	switch(traffic){
	case(0): cout << "Uniform\n"; break;
	case(1): cout << "Compliment\n"; break;
	case(2): cout << "Hotspots at node: ";
		for (a = 0; a < numHotspots; a++){
			cout << hotspots[a] << " ";
		}
		cout << "    % of Traffic: " << hotPercent << endl; break;
	case(3): cout << "Localized, % Local: " << local*100 << endl; break;
	case(5): cout << "Transpose pairs at nodes: ";
		for (a = 0; a < numTranspose; a++)
		{
			cout << "(" << transpose[a][0] << "/" << transpose[a][1] << ") ";
		}
		cout << "    % of Traffic: " << transPercent << endl; break;
	case(6): cout << "FFT Traffic" << endl; break;
	}
	cout << "9 - Load: " << load << endl;
	cout << "a - Message Length (flits): " << msgl << endl;
	if (SAT) cout << "b - Packets dropped when source queue overloads\n";
	else cout << "b - Simulation stops when source queue overloads\n";
	if (GHOST) cout << "c - Control flits used\n";
	else cout << "c - Control flits not used\n";
	if (DUMP) cout << "d - Message info dumped to messages.txt\n";
	else cout << "d - Message info not dumped\n";
	if (PORTSDUMP) cout << "e - Port contents dumped to ports.txt\n";
	else cout << "e - Port info not dumped\n";
	if (PRINTADJ) cout << "f - Ajacentcy list dumped to adjlist.txt\n";
	else cout << "f - Adjacentcy list not dumped\n";
	if (AVGQ) cout << "g - Average Queue Length calculation is ON\n";
	else cout << "g - Average Queue Length calculation is OFF\n";
	cout << "h - Stat update interval: " << step << endl;
	if (ACTMSGS) cout << "i - Average Active Messages calculation is ON\n";
	else cout << "i - Average Active Messages calculation is OFF\n";
	cout << "j - Header Collisions handled by: ";
	switch (select_function){
	case(0): cout << "Port Order\n"; break;
	case(1): cout << "Oldest Goes First\n"; break;
	case(2): cout << "Round Robin\n"; break;
	case(3): cout << "Priority Scheme\n"; break;
	}
	if (RUNONCE) cout << "k - 1 interation per cycle\n";
	else cout << "k - Unlimited iterations per cycle\n";
	if (USETRACE) cout << "l - Using traffic info from trace.txt\n";
	else cout << "l - Not using trace file\n";
	if (injection_type == POISSON) cout << "m - Poisson Distribution\n";
	else cout << "m - Self-Similar Distribution\n";
	cout << "\nDerived Parameters: \n";
	cout << "Switches: " << numSwitches << "\nNodes: " << numNodes << endl << "Ports: " << numPorts << endl;
	if (top_type==BFT || top_type==KARY || top_type==OCTO) cout << "Levels: " << levels << endl;

	if (runs>1) cout << "Sweep of " << runs << " values\n";

}

void get_args(int argc, char *argv[])
{
	CCmdLine cmdLine;
	string str;

	int k, t, n,a;
	int num_clusters;
	char p, y_or_n;
	float f;

	if(cmdLine.SplitLine(argc, argv) < 1) {
		cout << "No switches given" << endl;
		exit(-1);
	}

	if(cmdLine.HasSwitch("-ip")){
		str = cmdLine.GetArgument("-ip", 0);
		numIps = atoi(str.c_str());
		if(numIps < 2)
			throw invalid_argument("Invalid number of IPs");
		cout << "Set number of IPs to " << numIps << endl;
	}
	if(cmdLine.HasSwitch("-t")){
		str = cmdLine.GetArgument("-t", 0);
		cout << "The topology type is " << str << endl;
		if(str == "BFT") {
			inject_port=4;
			numPorts=6;
			levels = (int)ceil(log((double)numIps)/log((double)4));
			numSwitches=0;
			for (a = 1; a <= levels; a++)
				numSwitches=numSwitches+numIps/(int)pow((float)2,(a+1));
			numNodes=numIps+numSwitches;
			top_type=BFT;
		}
		else if(str == "RING") {
			inject_port=0;
			numPorts=3;
			top_type=RING;
		}
		else if(str == "OCT") {
			inject_port=0;

			if (numIps==256) {
				numNodes=512;
				top_type=OCTOM256;
				octoDim=3;
				numPorts=10;
			}
			else {
				top_type=OCTOM; 
				numNodes=128;
				numIps=64;
				octoDim=2;
				numPorts=7;
			}
		}
		else if(str == "KARY") {
			string k_str,n_str;
			k_str = cmdLine.GetArgument("-t", 1);
			n_str = cmdLine.GetArgument("-t", 2);
			k = atoi(k_str.c_str());
			n = atoi(n_str.c_str());
			if (k<=0 || n<=0)
				throw invalid_argument("Invalid n or k");
			numPorts=2*k;
			numIps=(int)pow((float)k,n);
			levels = (int)ceil(log((double)numIps)/log((double)k));
			inject_port=k;
			numSwitches=n*(int)pow((float)k,(n-1));
			numNodes=numIps+numSwitches;
			top_type = KARY; 
			numIpsUsed=numIps;
			cout << "This is a " << k << "-ary " << n << "-tree" << endl;
		}
		else if(str=="MESH" || str=="TORUS") {
			string str2;
			dimensions = cmdLine.GetArgumentCount("-t") - 1;
			if(dimensions<1)
				throw invalid_argument("Invalid number of dimensions in cube");

			maxDim = 0;
			cube_dimensions = (int*) calloc(dimensions,sizeof(int));

			cout << "This is a " << dimensions << " dimension " << str << " with dimensions of: ";
			for (int a=0; a< dimensions; a++){
				str2 = cmdLine.GetArgument("-t", a+1);
				cube_dimensions[a] = atoi(str2.c_str());
				if(cube_dimensions[a]<1)
					throw invalid_argument("Invalid dimension values");
				if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
				cout << cube_dimensions[a] << " ";
			}
			cout << endl;
			numPorts=2*dimensions+1;
			numIps=1;
			for (int b=0;b<dimensions;b++)
				numIps=numIps*cube_dimensions[b];
			numSwitches=numIps;
			inject_port=0;
			numNodes=numIps+numSwitches;
			top_type = CUBE;
			if(str=="MESH") {
				WRAP=0;
			}
			else {
				WRAP=1;
				if(numVirts==1) numVirts=2;
			}
			numIpsUsed=numIps;
		}
		else if(str == "HBUS") {
			ips_per_bus=numIpsUsed/4;
			inject_port=0;
			numPorts=1;
			numVirts=1;
			top_type=HBUS;
			numNodes=numIps;
		}
		else if(str=="STACKED_M" || str=="STACKED_T") {
			string str2;
			dimensions = cmdLine.GetArgumentCount("-t") - 2;
			if(dimensions<1)
				throw invalid_argument("Invalid number of dimensions in mesh");

			maxDim = 0;
			cube_dimensions = (int*) calloc(dimensions+1,sizeof(int));

			cout << "This is a " << dimensions << " dimension " << str << " with dimensions of: ";
			for (int a=0; a<= dimensions; a++){
				str2 = cmdLine.GetArgument("-t", a+1);
				cube_dimensions[a] = atoi(str2.c_str());
				if(cube_dimensions[a]<1)
					throw invalid_argument("Invalid dimension values");
				if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
				cout << cube_dimensions[a] << " ";
			}
			num_layers = cube_dimensions[dimensions];
			cout << endl;
			numPorts = 2*dimensions+2;
			numIps=1;
			for (int b=0;b<dimensions;b++)
				numIps=numIps*cube_dimensions[b];
			num_buses = numIps;
			numIps *= num_layers;
			numSwitches = numIps;
			inject_port=0;
			numNodes = numIps+numSwitches+num_buses;
			top_type = STACKED;
			if(str=="STACKED_M") {
				WRAP=0;
			}
			else {
				WRAP=1;
				if(numVirts==1) numVirts=2;
			}
			numIpsUsed=numIps;
			/*					cin >> dimensions;
			maxDim = 0;
			cube_dimensions = (int*) calloc(dimensions+1,sizeof(int));
			for (int a=0; a< dimensions; a++){
			cout << "\nEnter nodes in dimension " << a+1 << ": ";	
			cin >> cube_dimensions[a];
			if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
			}
			num_layers = 0;
			while(num_layers <= 1) {
			cout << endl << "Enter number of layers to stack: ";
			cin >> num_layers;
			}
			cube_dimensions[dimensions]=num_layers;
			numPorts = 2*dimensions+2;
			numIps=1;
			for (int b=0;b<dimensions;b++)
			numIps=numIps*cube_dimensions[b];
			num_buses = numIps;
			numIps *= num_layers;
			numSwitches = numIps;
			inject_port=0;
			numNodes = numIps+numSwitches+num_buses;
			top_type = STACKED;
			cout << "\n0 - Mesh\n1 - Torus\nEnter 1 or 0:";
			cin >> t;
			if (t==0) WRAP=0;
			else if (t==1) WRAP=1;
			if (numVirts==1 && WRAP==1) numVirts=2;
			numIpsUsed=numIps;*/

		}
		else if(str=="CILIATED_M" || str=="CILIATED_T") {
			string str2;
			dimensions = cmdLine.GetArgumentCount("-t") - 2;
			if(dimensions<1)
				throw invalid_argument("Invalid number of dimensions in mesh");

			maxDim = 0;
			cube_dimensions = (int*) calloc(dimensions+1,sizeof(int));

			cout << "This is a " << dimensions << " dimension " << str << " with dimensions of: ";
			for (int a=0; a< dimensions; a++){
				str2 = cmdLine.GetArgument("-t", a+1);
				cube_dimensions[a] = atoi(str2.c_str());
				if(cube_dimensions[a]<1)
					throw invalid_argument("Invalid dimension values");
				if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
				cout << cube_dimensions[a] << " ";
			}
			str2 = cmdLine.GetArgument("-t", dimensions+1);
			ip_per_switch = atoi(str2.c_str());
			if(ip_per_switch<1)
				throw invalid_argument("Invalid number of IPs per switch");
			cout << "and " << ip_per_switch << " IPs per switch" << endl;
			cluster_bus_network = false;
			numIps=1;
			for (int b=0;b<dimensions;b++)
				numIps=numIps*cube_dimensions[b];
			num_clusters = numIps;
			numIps *= ip_per_switch;
			inject_port=0;
			if(cluster_bus_network) {
				numSwitches=num_clusters*2; // Half of these are buses
				numPorts=2*dimensions+1; 
			}
			else {
				numSwitches=num_clusters; // Every ip_per_switch IPs are connected to one switch
				numPorts=2*dimensions+ip_per_switch; // Note that there are ip_per_switch inject ports
			}
			numNodes=numIps+numSwitches;
			top_type = CLUSTERED;
			if(str=="CILIATED_M") {
				WRAP=0;
			}
			else {
				WRAP=1;
				if(numVirts==1) numVirts=2;
			}
			numIpsUsed=numIps;
		}
		else {
			throw invalid_argument("Invalid topology");
		}
	}
	if(cmdLine.HasSwitch("-buf")) {
		str = cmdLine.GetArgument("-buf", 0);
		bufferDepth = atoi(str.c_str());
		cout << "Buffer Depth: " << bufferDepth << endl;
	}
	if(cmdLine.HasSwitch("-vc")) {
		str = cmdLine.GetArgument("-vc", 0);
		numVirts = atoi(str.c_str());
		cout << "Virtual channels: " << numVirts << endl;
	}
	if(cmdLine.HasSwitch("-queue")) {
		str = cmdLine.GetArgument("-queue", 0);
		queueSize = atoi(str.c_str());
		cout << "Queue Length: " << queueSize << endl;
	}
	if(cmdLine.HasSwitch("-dur")) {
		str = cmdLine.GetArgument("-dur", 0);
		DUR = atoi(str.c_str());
		cout << "Duration: " << DUR << " cycles" << endl;
	}
	if(cmdLine.HasSwitch("-stat")) {
		str = cmdLine.GetArgument("-stat", 0);
		step = atoi(str.c_str());
		cout << "Stat update interval:" << step << endl;
	}
	if(cmdLine.HasSwitch("-r")) {
		str = cmdLine.GetArgument("-r", 0);
		reset = atoi(str.c_str());
		cout << "Reset time: " << reset << endl;
	}
	if(cmdLine.HasSwitch("-traffic")) {
		cout << "Traffic type" << endl;
		str = cmdLine.GetArgument("-t", 0);
		cout << "The distribution type is " << str << endl;
		if(str == "RANDOM") {
			traffic = 0;
		}
		else if(str == "COMP") {
			traffic = 1;
		}
		else if(str == "HOTSPOT") {
			traffic = 2;
			throw domain_error("Hotspot traffic not supported by cmd line arguments at this time");
		}
		else if(str == "LOCAL") {
			traffic = 3;
			str = cmdLine.GetArgument("-t", 1);
			local = atoi(str.c_str());
			if(local < 0.0 || local >1.0)
				throw invalid_argument("Invalid localization");
		}
		else if(str == "PILLAR") {
			traffic = 4;
			str = cmdLine.GetArgument("-t", 1);
			local = atoi(str.c_str());
			if(local < 0.0 || local >1.0)
				throw invalid_argument("Invalid localization");
		}
		else
			throw invalid_argument("Invalid localization type");
	}
	if(cmdLine.HasSwitch("-ss")) {
		injection_type = SS;
		cout << "Use self-similar distribution" << endl;
	}
	if(cmdLine.HasSwitch("-l")) {
		str = cmdLine.GetArgument("-l", 0);
		load = atof(str.c_str());
		cout << "Injeciton Load: " << load << endl;
	}
	if(cmdLine.HasSwitch("-ml")) {
		str = cmdLine.GetArgument("-ml", 0);
		msgl = atoi(str.c_str());
		cout << "Mesasge Length: " << msgl << endl;
	}
	if(cmdLine.HasSwitch("-nodrop")) {
		SAT = false;
		cout << "Do not drop flits" << endl;
	}
	if(cmdLine.HasSwitch("-control")) {
		GHOST = true;
		cout << "Use control flits" << endl;
	}
	if(cmdLine.HasSwitch("-M")) {
		DUMP = true;
		cout << "Dump message info" << endl;
	}
	if(cmdLine.HasSwitch("-P")) {
		PORTSDUMP = true;
		cout << "Dump port info" << endl;
	}
	if(cmdLine.HasSwitch("-A")) {
		PRINTADJ = true;
		cout << "Dump adjacency info" << endl;
	}
	if(cmdLine.HasSwitch("-Q")) {
		AVGQ = true;
		cout << "Calculate Queue length" << endl;
	}
	if(cmdLine.HasSwitch("-Act")) {
		ACTMSGS = true;
		cout << "Calculate Avg. messages" << endl;
	}
	if(cmdLine.HasSwitch("-trace")) {
		USETRACE = true;
		cout << "Use trace file" << endl;
	}
	if(cmdLine.HasSwitch("-sweep")) {
		n = cmdLine.GetArgumentCount("-sweep");
		string sweep_param = cmdLine.GetArgument("-sweep", 0);
		cout << "There are " << n << " sweep parameters for sweeping " << sweep_param << endl;
		runs = n-1;
		cout << "Run a sweep for the following values: ";
		for(int i=1; i < n; i++){
			str = cmdLine.GetArgument("-sweep", i);
			vary[i-1] = atof(str.c_str());
			cout << ' ' << vary[i-1];
		}
		cout << endl;
		if(sweep_param == "VIRTS")
			varyParam = 1;
		else if(sweep_param == "MSGL")
			varyParam = 2;
		else if(sweep_param == "BUFF")
			varyParam = 3;
		else if(sweep_param == "QUEUE")
			varyParam = 4;
		else if(sweep_param == "LOCAL")
			varyParam = 5;
		else if(sweep_param == "LOAD")
			varyParam = 6;
		else if(sweep_param == "HOTSPOT")
			varyParam = 7;
		else if(sweep_param == "PILLAR")
			varyParam = 8;
		else
			throw invalid_argument("That sweep is not supported");
		switch(varyParam) {
		case(1): numVirts=(int)find_largest_param(); break;
		case(3): bufferDepth=(int)find_largest_param(); break;
		case(4): queueSize=(int)find_largest_param(); break;
		case(5): traffic=3; break;
		case(8): traffic=4; break;
		}
		/*			case ('s'):  cout << "\nVirtual Channels - 1\nMessage Length - 2\nBuffer Depth - 3\n"
		<< "Source Queue Size - 4\nTraffic Localization - 5\nLoad - 6\nHotspot % - 7\nPillar Localization - 8\n";
		cout << "Enter paramter to vary: ";
		cin >> varyParam;
		cout << "Enter number of runs: ";
		cin >> runs;
		if (runs==99) { 
		for (int b=0; b < 4; b++){
		for (int c=0; c<11;c++){
		vary[b*11+c]=0.1*c;
		if (c==0) vary[b*11+c]=0.01;
		}
		}
		runs=33;
		}
		else {
		for (int a = 1; a<=runs; a++){
		cout << "Enter value " << a << " : ";
		cin >> vary[a-1];
		}
		}
		switch(varyParam){ 
		case(1): numVirts=(int)find_largest_param(); break;
		case(3): bufferDepth=(int)find_largest_param(); break;
		case(4): queueSize=(int)find_largest_param(); break;
		case(5): traffic=3; break;
		case(8): traffic=4; break;
		}break;*/
	}


}

/* display menu for changing network parameters*/
void menu(){
	int k, t, n,a;
	int num_clusters;
	char p, y_or_n;
	float f;
	// p = -1;		// manual config
	p = 'n';		// yuchen: autoconfig
	printParameters();

	// while (p!='r' && p!='q'){ // loop to print menu
  cout << "\nCOMMANDS: Run - r Setup Sweep - s Quit - q";
  cout << endl << "Enter number to change parameter, or choose a command to run simulation:  ";
  // cin >> p; 	// manual config
  switch(p){
  case('1'):  cout << " BFT - 0\n Ring - 1\n Octagon - 2\n K-ary N-Tree - 3\n K-ary N-Cube - 4\n HBUS - 5\n Cluster-based MESH - 6\n Stacked MESH - 7\n Super Switch - 8\n";
    cout << "Enter New Topology Type: ";
    cin >> t;
    switch(t){
      // Butterfly Fat Tree
    case(0): cout << endl << "Butterfly Fat Tree" << endl;
      inject_port=4;
      numPorts=6;
      levels = (int)ceil(log((double)numIps)/log((double)4));
      numSwitches=0;
      for (a = 1; a <= levels; a++)
	numSwitches=numSwitches+numIps/(int)pow((float)2,(a+1));
      numNodes=numIps+numSwitches;
      top_type=BFT; break;
      // Ring
    case(1): cout << endl << "Ring" << endl;
      inject_port=0;
      numPorts=3;
      top_type=RING;	break;
      // Octagon
    case(2): cout << endl << "Octagon" << endl;
      inject_port=0;

      if (numIps==256) {
	numNodes=512;
	top_type=OCTOM256;
	octoDim=3;
	numPorts=10;
      }
      else {
	top_type=OCTOM; 
	numNodes=128;
	numIps=64;
	octoDim=2;
	numPorts=7;
      }
      break;
      // K-ary N-Tree
    case(3): cout << endl << "Enter k: ";
      cin >> k;
      cout << "\nEnter n: ";
      cin >> n;
      if (k>0) numPorts=2*k;		
      if (n>0) numIps=(int)pow((float)k,n);
      levels = (int)ceil(log((double)numIps)/log((double)k));
      inject_port=k;
      numSwitches=n*(int)pow((float)k,(n-1));
      numNodes=numIps+numSwitches;
      top_type = KARY; 
      numIpsUsed=numIps;	break;
      // K-ary N-Cube
    case(4): cout << endl << "Enter number of dimesions: ";
      cin >> dimensions;
      maxDim = 0;
      cube_dimensions = (int*) calloc(dimensions,sizeof(int));
      for (int a=0; a< dimensions; a++){
	cout << "\nEnter nodes in dimension " << a+1 << ": ";	
	cin >> cube_dimensions[a];
	if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
      }
      numPorts=2*dimensions+1;
      numIps=1;
      for (int b=0;b<dimensions;b++)
	numIps=numIps*cube_dimensions[b];
      numSwitches=numIps;
      inject_port=0;
      numNodes=numIps+numSwitches;
      top_type = CUBE;
      cout << "\n0 - Mesh\n1 - Torus\nEnter 1 or 0:";
      cin >> t;
      if (t==0) WRAP=0;
      else if (t==1) WRAP=1;
      if (numVirts==1 && WRAP==1) numVirts=2;
      numIpsUsed=numIps; break;
      // HBUS
    case(5):ips_per_bus=numIpsUsed/4;
      inject_port=0;
      numPorts=1;
      numVirts=1;
      top_type=HBUS;
      numNodes=numIps;  break;
      // Ciliated MESH
    case(6): cout << endl << "Enter number of dimesions: ";
      cin >> dimensions;
      maxDim = 0;
      cube_dimensions = (int*) calloc(dimensions,sizeof(int));
      for (int a=0; a< dimensions; a++){
	cout << "\nEnter nodes in dimension " << a+1 << ": ";	
	cin >> cube_dimensions[a];
	if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
      }
      cout << endl << "Enter number of IPs per switch: ";
      cin >> ip_per_switch;
      if(ip_per_switch > 1) {
	cout << endl << "Are these connected via a cluster bus? (y/n): ";
	cin >> y_or_n;
	switch(y_or_n) {
	case 'n': cluster_bus_network = true;
	case 'y': cluster_bus_network = false;
	default: y_or_n = 'n';
	}
      }
      else
	ip_per_switch = 1;
      numIps=1;
      for (int b=0;b<dimensions;b++)
	numIps=numIps*cube_dimensions[b];
      num_clusters = numIps;
      numIps *= ip_per_switch;
      inject_port=0;
      if(cluster_bus_network) {
	numSwitches=num_clusters*2; // Half of these are buses
	numPorts=2*dimensions+1; 
      }
      else {
	numSwitches=num_clusters; // Every ip_per_switch IPs are connected to one switch
	numPorts=2*dimensions+ip_per_switch; // Note that there are ip_per_switch inject ports
      }
      numNodes=numIps+numSwitches;
      top_type = CLUSTERED;
      cout << "\n0 - Mesh\n1 - Torus\nEnter 1 or 0:";
      cin >> t;
      if (t==0) WRAP=0;
      else if (t==1) WRAP=1;
      if (numVirts==1 && WRAP==1) numVirts=2;
      numIpsUsed=numIps; break;
    case(7): cout << endl << "Enter number of dimesions in base: ";
      cin >> dimensions;
      maxDim = 0;
      cube_dimensions = (int*) calloc(dimensions+1,sizeof(int));
      for (int a=0; a< dimensions; a++){
	cout << "\nEnter nodes in dimension " << a+1 << ": ";	
	cin >> cube_dimensions[a];
	if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
      }
      num_layers = 0;
      while(num_layers <= 1) {
	cout << endl << "Enter number of layers to stack: ";
	cin >> num_layers;
      }
      cube_dimensions[dimensions]=num_layers;
      numPorts = 2*dimensions+2;
      numIps=1;
      for (int b=0;b<dimensions;b++)
	numIps=numIps*cube_dimensions[b];
      num_buses = numIps;
      numIps *= num_layers;
      numSwitches = numIps;
      inject_port=0;
      numNodes = numIps+numSwitches+num_buses;
      top_type = STACKED;
      cout << "\n0 - Mesh\n1 - Torus\nEnter 1 or 0:";
      cin >> t;
      if (t==0) WRAP=0;
      else if (t==1) WRAP=1;
      if (numVirts==1 && WRAP==1) numVirts=2;
      numIpsUsed=numIps;
      break;
      //SUPER SWITCH
    case(8): cout << endl << "(Enter 1 for random connection)\nEnter number of dimesions: ";
      cin >> dimensions;
      maxDim = 0;
      cube_dimensions = (int*) calloc(dimensions,sizeof(int));
      for (int a=0; a< dimensions; a++){
	cout << "\nEnter nodes in dimension " << a+1 << ": ";	
	cin >> cube_dimensions[a];
	if (cube_dimensions[a]>maxDim) maxDim=cube_dimensions[a];
      }
      cout << endl << "Enter number of max ports per switch: ";
      cin >> numPorts;
      cout << endl << "Enter number of Ips: ";
      cin >> numIps;
      cout << endl << "Enter number of Switches: ";
      cin >> numSwitches;

      inject_port=0;
      numNodes=numIps+numSwitches;
      numIpsUsed=numIps;

      top_type = SUPERS;

      int tnode = 0;
      failure = 0;
      traffic_optim = 0;

      cout << endl << "Enter 5 if you want a random connected network: ";
      cin >> tnode;

      cout << endl << "Use traffic parameters to connect network? (1 for yes)";
      cin >> traffic_optim;

      if(traffic_optim)
	cout << "Traffic will be accounted for when making connections!" << endl;
      else
	cout << "Proceeding like normal..." << endl;


      cout << endl << "Enter 1 if you want to add wireless connections: ";
      cin >> optim;

      if (optim == 1)
	{
	  cout << endl << "Enter number of Wireless connections: ";
	  cin >> numWireless;
	  cout << endl << "Enter the percentage of wireless failures: ";
	  cin >> numFail;
	  if (numFail == 0)
	    failure = 0;
	  else
	    failure = 1;
	}
      else
	{
	  optim = 0;
	  cout << endl << "No wireless connections will be made,";
	}

      if (tnode == 5)
	{
	  int kmax = 0;
	  int ks = 0;
	  double alpha = 0;
	  cout << endl << "Enter in ks (average ports per switch): ";
	  cin >> ks;
	  cout << "Enter in kmax (max ports per switch): ";
	  cin >> kmax;
	  cout << "Enter in alpha (connectivity parameter): ";
	  cin >> alpha;
	  make_connect_rand(numIps, numSwitches, ks, kmax, alpha);
	  connection_type = 5;
	}
      else
	{
	  cout << "CONNECTION hasnt been made yet,\nerrors will happen until fixed" << endl << endl;
	  connection_type = 0;
	}

      tnode = 0;
      cout << "\n\n\nI have made it this far!\n\n\n";
      //connection needs to be made before this step else failure!!!
      break;
    }	break;
  case('2'): cout << "Enter new number of IPs: ";
    cin >> t;
    if (t>0) { numIpsUsed = t; numIps = t; }
    if (top_type==BFT) {levels = (int)ceil(log((double)numIpsUsed)/log((double)4)); }
    else if (top_type==KARY) {levels = (int)ceil(log((double)numIpsUsed)/log((double)numPorts/2));}
    numIps=(int)pow((float)4,levels);
    if (top_type==BFT) {
      numSwitches=0;
      for (a = 1; a <= levels; a++)
	numSwitches=numSwitches+numIps/(int)pow((float)2,(a+1));
    }
    else if (top_type == KARY)
      numSwitches=levels*numIps/(numPorts/2);
    else if (top_type==HBUS){
      ips_per_bus = numIpsUsed/4;
      numIps=numIpsUsed;
    }
    numNodes=numIps+numSwitches; break;
  case ('3'): cout << "Enter new buffer depth in flits: ";
    cin >> t;
    if (t>0) bufferDepth=t;  break;
  case ('4'): cout << "Enter new number of virtual channels: ";
    cin >> t;
    if (t>0) numVirts=t;  break;
  case ('5'): cout << "Enter new source queue length (messages): ";
    cin >> t;
    if (t>0) queueSize=t;  break;
  case ('6'): cout << "Enter new simulation duration: ";
    cin >> t;
    if (t>0) DUR=t;  break;
  case ('7'): cout << "Enter new reset time: ";
    cin >> t;
    if (t>0) reset=t;	  break;
  case ('8'): cout << "\n Uniform Random - 0\n Complement - 1\n Hotspot - 2\n Localized - 3\n Pillar - 4\n Transpose - 5\n FFT - 6\n Matrix Multiplication - 7\n";
    cout << "Enter new traffic distribution: ";
    cin >> t;
    if (t>=0) 
      traffic=t;
    if (t==3) 
      { 
	cout << "Enter fraction of messages that are local (0-1): ";
	cin >> f;
	local=f;
      }	 
    if (t==4) 
      { 
	cout << "Enter fraction of messages transmitted in the pillar (0-1): ";
	cin >> f;
	local=f;
      }	 
    if (t == 5) //TRANSPOSE PAIRS
      {
	cout << "Enter # of transpose pairs: ";
	cin >> t;
	if (t > 0)
	  {
	    numTranspose = t;
	    transpose = (int**) calloc(numTranspose, sizeof(int*));
	    con_transpose = (int**) calloc(numTranspose, sizeof(int*));
	    for(int a = 0; a < numTranspose; a++)
	      {
		transpose[a] = (int*) calloc(2, sizeof(int));
		con_transpose[a] = (int*) calloc(2, sizeof(int));
		cout << "\nEnter the transpose node pair " << a+1 << ", seperated by a space (ex: 2 13): ";
		cin >> t;
		transpose[a][0] = t;
		cin >> t;
		transpose[a][1] = t;
	      }
	    cout << "\nEnter % of traffic that will be transpose communication (0-100): ";
	    cin >> t;
	    if (t >= 0)
	      {
		transPercent = t;									
	      }
	  }
      }
    if (t == 6) //FFT
      {
	cout << endl << endl << "The traffic pattern will now be FFT" << endl << endl;
	int xi;
	double xk;
	double xm;
	double xj;
	FFTmatrix = (int**) calloc(numIps, sizeof(int*));
	for(xi = 0; xi < numIps; xi++)
	  {
	    FFTmatrix[xi] = (int*) calloc(numIps, sizeof(int));
	  }


	for(xi = 1; xi <= (log((double) numIps)/log(2.0)); xi++)
	  {
	    xm = pow(2.0, xi);
	    xk = 1;
	    while(k < numIps)
	      {
		xj = 0;
		while(xj < (xm/2))
		  {
		    FFTmatrix[(int) (xk + xj)-1][(int) (xk + xj + (xm/2))-1] = 1;
		    FFTmatrix[(int) (xk + xj + (xm/2))-1][(int) (xk + xj)-1] = 1;
		    xj += 1;
		  }
		xk += xm;
	      }
	  }

	for(xi = 0; xi < numIps; xi++)
	  {
	    for(int xii = 0; xii < numIps; xii++)
	      {
		FFTmatrix[xi][xii] *= 100;
		FFTmatrix[xi][xii] /= (log((double) numIps)/log(2.0));
	      }
	  }
      }
    if (t == 7) //Matrix Multiplication
      {

      }
    if (t==2) //HOTSPOT
      { 
	cout << "Enter # of hotspots: ";
	cin >> t;
	if (t>0) 
	  {
	    numHotspots=t;
	    hotspots = (int*) calloc (numHotspots,sizeof(int));
	    con_hotspots = (int*) calloc(numHotspots, sizeof(int));
	    for (int a =0; a < numHotspots; a++)
	      {
		cout << "Enter node location of hotspot " << a+1 << ":";
		cin >> t;
		if (t>=0 && t<numIps) hotspots[a]=t;
	      }
	  }
	cout << "Enter % of traffic that will be destined for a hotspot: ";
	cin >> t;
	if (t>=0) hotPercent=t;
      }
    break;
  case ('9'): cout << "Enter new load (0-1): ";
    cin >> f;
    if (f>=0) load= f;	  break;
  case ('a'): cout << "Enter new message length: ";
    cin >> t;
    if (t>0) msgl=t;  break;
  case ('b'): SAT=!SAT; break;
  case ('c'): GHOST=!GHOST; break;
  case ('d'): DUMP=!DUMP; break;
  case ('e'): PORTSDUMP=!PORTSDUMP; break;
  case ('f'): PRINTADJ=!PRINTADJ; break;
  case ('g'): AVGQ=!AVGQ; break;
  case ('h'): cout << "Enter new update interval: ";
    cin >> t;
    if (t>0) step=t; break;
  case ('i'): ACTMSGS=!ACTMSGS; break;
  case ('j'): cout << "\nPort Order - 0\nOldest Goes First - 1\nRound Robin - 2\nPriority Scheme - 3\n"
		   << "Please enter select function: "; 
    cin >> select_function; break;
  case ('k'): RUNONCE=!RUNONCE; break;
  case ('l'): USETRACE=!USETRACE; break;
  case ('m'): injection_type = !injection_type; break;
		
  case ('n'): cout<<"new mac:"<<endl; 
    {	
      if(fMESH)
	{
	  dimensions=2;
	  cube_dimensions = (int*) calloc(dimensions,sizeof(int));
	  cube_dimensions[0]=8;
	  cube_dimensions[1]=8;
	  numPorts=2*dimensions+1;
	  numIps=1;
	  for (int b=0;b<dimensions;b++)
	    numIps=numIps*cube_dimensions[b];
	  numSwitches=numIps;
	  inject_port=0;
	  numNodes=numIps+numSwitches;
	  top_type = CUBE;
	  t=0;
	  if (t==0) WRAP=0;
	  else if (t==1) WRAP=1;
	  if (numVirts==1 && WRAP==1) numVirts=2;
	  numIpsUsed=numIps; 
	  // HBUS
	  load=2.0;
	  runs=1;
	  bufferDepth=2;
	}
      else
	{
	  dimensions=1;
	  //CUSTOM_MAC = true;
	  maxDim = 0;
	  cube_dimensions = (int*) calloc(dimensions,sizeof(int));
	  cube_dimensions[0]=64;
	  if (cube_dimensions[0]>maxDim) maxDim=cube_dimensions[0];

	  numPorts = 17;
	  numIps=64;
	  numSwitches=64;

	  inject_port=0;
	  numNodes=numIps+numSwitches;
	  numIpsUsed=numIps;

	  top_type = SUPERS;
	  failure = 0;
	  traffic_optim = 0;
	  optim=0;

	  int tnode = 5;
	  int kmax = 7;
	  int ks = 4;
	  double alpha = 1.8;
	  make_connect_rand(numIps, numSwitches, ks, kmax, alpha);
	  connection_type = 5;
	  bufferDepth=2;
	  runs=1;

	}
			
    }
    break;

  case ('q'):  cout << "QUIT"; runs =0 ;break;
  case ('s'):  cout << "\nVirtual Channels - 1\nMessage Length - 2\nBuffer Depth - 3\n"
		    << "Source Queue Size - 4\nTraffic Localization - 5\nLoad - 6\nHotspot % - 7\nPillar Localization - 8\nWindow Size -9\n";
    cout << "Enter paramter to vary: ";
    cin >> varyParam;
    cout << "Enter number of runs: ";
    cin >> runs;
    if (runs==99) { 
      for (int b=0; b < 4; b++){
	for (int c=0; c<11;c++){
	  vary[b*11+c]=0.1*c;
	  if (c==0) vary[b*11+c]=0.01;
	}
      }
      runs=33;
    }
    else {
      for (int a = 1; a<=runs; a++){
	cout << "Enter value " << a << " : ";
	cin >> vary[a-1];
      }
    }
    switch(varyParam){ 
    case(1): numVirts=(int)find_largest_param(); break;
    case(3): bufferDepth=(int)find_largest_param(); break;
    case(4): queueSize=(int)find_largest_param(); break;
    case(5): traffic=3; break;
    case(8): traffic=4; break;
    }break;

  }
  //clear screen somehow here
  for (int a =0; a < 10; a++)
    cout << endl << endl << endl << endl << endl;
  printParameters();
  // } // loop to print menu
}

// retrieves the next 
void get_next_trace(){
	if (! traceFile)
	{
		cout << "Error opening input file - get next" << endl;
		//     return -1;
	}

	int time, src;
	traceFile >> time >> src;
	cout << time << " " << src << endl;

}

// RUN FUNCTION ***********************************
int main (int argc, char *argv[]) 
{
  assert(argc == 3);
  string benchmark0 = argv[1];
  if (benchmark0 == "fft")
    fFFT = true;
  else if (benchmark0 == "radix")
    fRADIX = true;
  else if (benchmark0 == "lu")
    fLU = true;
  else if (benchmark0 == "water")
    fWATER = true;
  else if (benchmark0 == "canneal")
    fCANNEAL = true;
  else if (benchmark0 == "dedup")
    fDEDUP = true;
  else if (benchmark0 == "fluidanimate")
    fFLUIDANIMATE = true;
  else if (benchmark0 == "vips")
    fVIPS = true;
  else if (benchmark0 == "combined")
    fcombined = true;
  else
    assert(false);
  flit_hop_count = 0;
  total_flit_count = 0;

	resultFile<<"Benchmark\tLatecncy\tMessages done\tWireless messages\tSwitch Energy\tInterconnect Energy\tTotal Energy\tAverage energy Per Message"<<endl;

	if(!cluster.is_open())
	{
		cluster.open("cluster_regular.txt", fstream::in);
	}

	for(int i = 0; i < NUM_IPS; i++)
	{
		cluster >> clusterMatrix[i];
	}
	
	if(!vfiInput.is_open())
	{
		vfiInput.open("vfi.txt", fstream::in);
	}
	for(int i = 0; i < 4; i++)
	{
		vfiInput >> vfiClustering[i];
	}

	for(int i = 0; i < NUM_IPS; i++)
	{
		for(int j = 0; j < NUM_IPS; j++)
		{
			for(int k = 0; k < 4; k++)
			{
				messageVfiTotal[i][j][k] = 0;
			}
		}
	}

	maxLatency=2000;
	//LAT=false;

	GATEDUMP=0;
	TEST=0;	

	octoTraffic = 1;

	setDefaults();		// yuchen: get_args intercept args, bypassed
	// if(argc > 1) {
	// 	cout << "There are " << argc << " arguments." << endl;
	// 	get_args(argc, argv);
	// }
	// else
	menu();
	// assert(false);

	int initialTime = time(NULL);

	for(int i = 0; i < NUM_IPS; i++)
	{
		for(int j = 0; j < NUM_IPS; j++)
		{
			latencyPairs[i][j] = 0;
			messageTotal[i][j] = 0;
		}
	}
 
	//Cartesian Distance Calculation - Karthi


	//Link energy stuff - calculation of cartesian distances

	int temp_row1;
	int temp_row2;
	int temp_column1;
	int temp_column2;
	int temp_row_diff;
	int temp_column_diff;
	int test_sum_distance=0;

	for(int a=0;a<numSwitches;a++)
	{
		for(int b=0;b<numSwitches;b++)
		{
			temp_row1=a/8;
			temp_row2=b/8;
			temp_column1=a%8;
			temp_column2=b%8;
		
			temp_row_diff=abs(temp_row1-temp_row2);
			temp_column_diff=abs(temp_column1-temp_column2);
			//cout<<a<<"\t"<<b<<"\t"<<temp_row1<<"\t"<<temp_row2<<"\t"<<temp_row_diff<<"\t"<<temp_column1<<"\t"<<temp_column2<<"\t"<<temp_column_diff<<endl;
			//link_manhattan_distance[a][b]=temp_column_diff+temp_row_diff;

			temp_row_diff=temp_row_diff*temp_row_diff;
			temp_column_diff=temp_column_diff*temp_column_diff;
			link_cartesian_distance[a][b]=floor(sqrt(temp_row_diff+temp_column_diff));
			test_sum_distance+=link_cartesian_distance[a][b];
		}
	}
	//cout<<"Testsum of cartesain distances:"<<test_sum_distance<<"\n";

	//wireless channel assignment

	for(int count0 = 0; count0 < 5; count0++)
	{
		wireless_node[channel_1_switch[count0]]=1;
		wireless_node[channel_3_switch[count0]]=3;
		if(count0 < 4)
		{
			wireless_node[channel_2_switch[count0]]=2;
		}
		
		//cout<<"wireless node value: node "<<channel_1_switch[count0]<<"wireless value:"<<wireless_node[channel_1_switch[count0]]<<endl;
	}
	wireless_node[GATEWAY]=4;

	
	//	srand((unsigned int) time(NULL));
	for(int z = 1; z <=runs; z++)
	{

	flit_hop_count = 0;
	total_flit_count = 0;

	initbenchmark__flags();

	if(z<6 && !fMESH)
	{
		DC_MAC=false;	
		TOKEN_MAC=true;
		fSTART=true;
	}
	else if(!fMESH)
	{
		TOKEN_MAC=false;
		DC_MAC=true;
		fSTART=false;
	}

	 
			
	if(fCANNEAL)
	{
		sprintf (path_filename, "paths_alash_wi_canneal.txt",wirelessPathThreshold);
		sprintf (benchmark, "CANNEAL");
	}
	if(fFFT)
	{
		sprintf (path_filename, "paths_alash_wi_fft.txt");
		sprintf (benchmark, "FFT");
	}
	if(fLU)
	{
		sprintf (path_filename, "paths_alash_wi_lu.txt");
		sprintf (benchmark, "LU");
	}
	if(fRADIX)
	{
		sprintf (path_filename, "paths_alash_wi_radix.txt");
		sprintf (benchmark, "RADIX");
	}
	if(fBODYTRACK)
	{
		sprintf (path_filename, "paths_alash_wi_bodytrack.txt");
		sprintf (benchmark, "BODYTRACK");
	}

//	srand(time(NULL));			// initialize random seed
	
	if(fBENCHMARK)
		initialize_benchmarks();

	initialize_network(argv[2]);
	initWirelessTokens();
	makeFij();
	if(fCANNEAL || fFLUIDANIMATE)
		srand(11223345);
	else if(fFREQMINE)
		srand(12312412);
	else if(fBODYTRACK10)
		srand(12512412);
	else if(fBODYTRACK30)
		srand(11223344);
	else if(fBODYTRACK60)
		srand(12312312);
	else if(fBODYTRACK70)
		srand(12312315);
	else if(fBODYTRACK80)
		srand(12351241);
	else
		srand(11223346); 


		for(int temp_count3 = 0; temp_count3 < 2432; temp_count3++)
		{
			link_flit_counter[temp_count3] = 0;
		}

		for(int temp_count4 = 0; temp_count4 < 128; temp_count4++)
		{
			node_flit_counter[temp_count4] = 0;
		}
		
	
		if (traceFile.is_open()) traceFile.close();
		switch(varyParam){
		case(1): if (vary[z-1]>0) numVirts=(int)vary[z-1]; break;
		case(2): if (vary[z-1]>0) msgl=(int)vary[z-1]; break;
		case(3): if (vary[z-1]>0) bufferDepth=(int)vary[z-1]; break;
		case(4): if (vary[z-1]>0) queueSize=(int)vary[z-1]; break;
		case(5): if (vary[z-1]>=0) local=vary[z-1]; break;
		case(6): if (vary[z-1]>=0) load=vary[z-1]; 
			if (USETRACE) {
				if ((float)vary[z-1]==(float)0.01) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.01.txt",fstream::in);
					DUR=1000000;
				}
				if ((float)vary[z-1]==(float)0.1) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.1.txt",fstream::in);
					DUR=1000000;
				}
				if ((float)vary[z-1]==(float)0.2) {
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.2.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.3) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.3.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.4) {
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.4.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.5) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.5.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.6) {
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.6.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.7) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.7.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.8) {
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.8.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)0.9) {	// return to start of file
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace0.9.txt",fstream::in);
				}
				if ((float)vary[z-1]==(float)1.0) {
					if (traceFile.is_open()) traceFile.close();
					traceFile.open("trace1.0.txt",fstream::in);
				}
			}

			break;
		case(7): if (vary[z-1]>=0) hotPercent=(int)vary[z-1];break;
		case(8): if (vary[z-1]>=0) local=vary[z-1]; break;
		case(9): if (vary[z-1]>=0) windowSize=vary[z-1]; break;

		}

		cout << "\nTreeSim     run=" << z << endl;
		cout << "Topology Type: " << top_type << endl;
		cout << numNodes << " Nodes, " << numIps << " IPs\n";
		cout << numVirts << " Virtual Channels, " << bufferDepth << " Buffer Depth\n";
		cout << "Message length: " << msgl << endl;
		cout << "Queue Size: " << queueSize << endl;
		cout << "Load: " << load << endl;
		cout << "Duration - reset: " << DUR-reset << endl;
		cout << "Window Size: " << windowSize << endl;
		if (traffic ==3 || traffic==4) cout << "local: " << local << endl;

		reinitialize_network();
		
	
		if(top_type == SUPERS && fWIRELESS)
		{
			tokenPacketCount[0] = 0;
			tokenPacketCount[1] = 0;
			tokenPacketCount[2] = 0;
			initWirelessTokens();
		}

		for (cycles=0; cycles < DUR; cycles++){
			treeToken = (treeToken + 1) % MTREES;

			if(SOFT_RESET)
			{
				if((cycles % windowSize) == 0)
				{
					for(int p = 0; p < numNodes; p++)
					{
						for(int q = 0; q < numNodes; q++)
						{
							for(int r = 0; r < numLayers; r++)
							{
								communication_density[p][q][r] /= windowSize;
							}
						}
					}
				}
			}
			else if(HARD_RESET)
			{
				if((cycles % windowSize) == 0)
				{
					for(int p = 0; p < numNodes; p++)
					{
						for(int q = 0; q < numNodes; q++)
						{
							for(int r = 0; r < numLayers; r++)
							{
								communication_density[p][q][r] = 0;
							}
						}
					}
				}
			}
			else if(fWEIGHTED)
			{
				if((cycles % windowSize) == 0)
				{
					for(int p = 0; p < numNodes; p++)
					{
						for(int q = 0; q < numNodes; q++)
						{
							for(int r = 0; r < numLayers; r++)
							{
								communication_density[p][q][r] /= WEIGHT;
							}
						}
					}
				}
			}
			if((cycles % WINDOW_SIZE) == 0)
			{
				for(int p = 0; p < MST_N; p++)
				{
					RT[p].commDensity /= WINDOW_SIZE;

					if (RT[p].commDensity > BETA) // Need to throttle links destined for router i.
					{
						RT[p].Throttled = true;
						RT[p].ThrottleAttempts++;
						RT[p].commDensity = 0.0;
						if(!GLOBAL)
						{
							updateRoutingTables(p); // Update routing tables for given neighboring routers of router i.
						}
					}
					else if (RT[p].Throttled) // If the router was a problem, but not anymore, stop throttling associated links.
					{
						RT[p].Throttled = false;
						RT[p].ThrottleAttempts = 0;
						if(!GLOBAL)
						{
							updateRoutingTables(p);
						}
					}
					RT[p].commDensity /= 2.0; // Reset commDensity for the next window
				}
			}

			//for(int q=0; q < maxMessage; q++){
			//	for(int p=0; p < 4; p++){
			//		if((msgs[q].dest[p] > 3) && (msgs[q].end_time==-2))
			//			printf("\n**Cycle=%d Message %d: Dest[%d]=%d**\n", cycles, q, p, msgs[q].dest[p]);
			//	}
			//}

			if(cycles == 700)
				cycles = cycles;

			if (cycles==reset-1) {		// reset stats to eliminate transient effects
				network_latency = 0;
				total_latency=0;
				total_latency0=0;
				total_latency1=0;
				total_latency2=0;
				total_latency3=0;
				messages_done=0;
				messages_done0=0;
				messages_done1=0;
				messages_done2=0;
				messages_done3=0;
				intranode_header_total=0;
				intranode_data_total=0;
				internode_total=0;
				internode_z=0;
				temp_intranode_data_total=0;
				temp_intranode_header_total=0;
				temp_internode_total=0;
				internode_local=0;
				internode_mid=0;
				internode_long=0;
				temp_internode_local=0;
				temp_internode_mid=0;
				temp_internode_long=0;
				avg_queue_size=0;
				temp_avg_queue_size=0;
				counter=0;
				activeMessages=0;
				local_bus_tot=0;
				far_bus_tot=0;
				wireless_done = 0;
				rerouted = 0;
				wirelesstaken = 0;
				wireless_usage = 0;
				total_wireless = 0;
				tr_msgs = 0;
				flitsInjected = 0;
				flitsConsumed = 0;
				flitsMoved = 0;
				for(int i = 0; i < NUM_IPS; i++)
				{
					for(int j = 0; j < NUM_IPS; j++)
					{
						latencyPairs[i][j] = 0;
						messageTotal[i][j] = 0;
						for(int k = 0; k < 4; k++)
						{
							messageVfiTotal[i][j][k] = 0;
						}
					}
				}

				for(int i = 0; i <numIps; i++)
				{
					wirelessUsage[i] = 0;
					for(int j = 0; j < numIps; j++)
					{
						flitsPerLink[i][j] = 0;
						if(fALASH)
							communicationPerLink[i][j] = 0;
						messagesInjected[i][j] = 0;
					}
				}
				communicationTotal = 0;
			}

			if (cycles % step == 0) {
				if (temp_done==0){
					cout << cycles << " temp done: " << temp_done << endl;
					cout << "\t temp header intra: " << (float)temp_intranode_header_total/step << " temp data intra: " << (float)temp_intranode_data_total/step << " temp internode: " << (float)temp_internode_total/step << " avg_q: " << (float)temp_avg_queue_size/(step*numIpsUsed) << endl;
				}
				else { 					

					cout << cycles << " temp done: " << temp_done <<  " temp tput: " << (float) (temp_done*(msgl))/(step*numIpsUsed) << " temp lat: "  << temp_lat/temp_done << endl;
					cout << " temp h: " << (float)temp_intranode_header_total/step << " temp d: " << (float)temp_intranode_data_total/step << " temp inter: " << (float)temp_internode_total/step << " avg_q: " << (float)temp_avg_queue_size/(step*numIpsUsed);
					cout << endl;
					if (top_type==OCTOM256){
						octoOut << cycles << " temp done: " << temp_done <<  " temp tput: " << (float) (temp_done*(msgl))/(step*numIpsUsed) << " temp lat: "  << temp_lat/temp_done << endl;
						octoOut << " temp h: " << (float)temp_intranode_header_total/step << " temp d: " << (float)temp_intranode_data_total/step << " temp inter: " << (float)temp_internode_total/step << " avg_q: " << (float)temp_avg_queue_size/(step*numIpsUsed);
						octoOut << "temp local int: " << (float) temp_internode_local/step << "temp mid int: " << (float) temp_internode_mid/step<< "temp long int: " << (float) temp_internode_long/step << endl;
					}
				}
				temp_done=0;
				temp_lat=0;
				temp_internode_local=0;
				temp_internode_mid=0;
				temp_internode_long=0;
				temp_intranode_header_total=0;
				temp_intranode_data_total=0;
				temp_internode_total=0;
				temp_avg_queue_size=0;
			}
			if (top_type!=HBUS) update_network();
			else update_bus_network();
			token++;
			if (token == numVirts) token = 0;
			port_token++;
			if (port_token == numPorts) port_token = 0;
			//port_token = int_rand(numPorts);
			if (TEST) DUMP=true;
						
			if(top_type == SUPERS && fWIRELESS)
			{
				if(DC_MAC)
					request_analyses();
				checkTokens();
				if(fMROOTS)
					updateWirelessLinks(token1, token2, token3);
			}
		}
		

		double internode_energy;
		if (top_type==CUBE)
			if(WRAP)
				internode_energy = (internode_total-internode_z) * (interconnect_energy*2) + (internode_z*interconnect_special);
			else
				internode_energy = (internode_total-internode_z) * (interconnect_energy) + (internode_z*interconnect_special);
		else if(top_type==STACKED)
			if(WRAP == 1)
				internode_energy = (internode_total-internode_z) * (interconnect_energy*2) + (internode_z*interconnect_bus);
			else
				internode_energy = (internode_total-internode_z) * (interconnect_energy) + (internode_z*interconnect_bus);
		else
			if(WRAP == 1)
				internode_energy = internode_total * (interconnect_energy*2);
			else
				internode_energy = internode_total * (interconnect_energy);
		double header_energy;
		double data_energy;
		if(top_type==STACKED) {
			header_energy = (intranode_header_total) * (total_router_energy) + (internode_z*bus_total);
			data_energy = (intranode_header_total) * (other_router_energy) + (internode_z*bus_total);
		}
		else {
			header_energy = intranode_header_total * (total_router_energy);
			data_energy = intranode_data_total * (other_router_energy);
		}

		total_energy = internode_energy + header_energy + data_energy; 

		for(int i = 0; i < NUM_IPS; i++)
		{
			for(int j = 0; j < NUM_IPS; j++)
			{
				if(i != j)
					pairwiseLatency << "Source:\t" << i << "\tDest:\t" << j << "\tLatency:\t" << latencyPairs[i][j] << "\tTotal:\t" << messageTotal[i][j] << "\tClusterTotals\t" << messageVfiTotal[i][j][0] << "\t" << messageVfiTotal[i][j][1] << "\t" << messageVfiTotal[i][j][2] << "\t" << messageVfiTotal[i][j][3] << "\t" << endl;
			}
		}

		outFile << "\nTreeSim\n";
		if(fCANNEAL)
			outFile << "Benchmark: CANNEAL" << endl;
		if(fBODYTRACK)
			outFile << "Benchmark: BODYTRACK" << endl;
		if(fLU)
			outFile << "Benchmark: LU" << endl;
		if(fRADIX)
			outFile << "Benchmark: RADIX" << endl;
		if(fFFT)
			outFile << "Benchmark: FFT" << endl;
		if(HARD_RESET)
			outFile << "Reset Type: HARD" << endl;
		if(SOFT_RESET)
			outFile << "Reset Type: Soft" << endl;
		outFile << numNodes << " Nodes, " << numIpsUsed << " IPs\n";
		outFile << numVirts << " Virtual Channels, " << bufferDepth << " Buffer Depth\n";
		if (GHOST) outFile << "Message length: " << (msgl-1) << endl;
		else outFile << "Message length: " << (msgl) << endl;
		outFile << "Load: " << load << endl;
		outFile << "Duration - reset: " << DUR-reset << endl;
		if (traffic ==3) outFile << "local: " << local << endl << "long: " << long_distance << endl;
		if (traffic ==4) outFile << "Pillar Localization: " << local << endl;
		outFile << "\n\n****************\nTesting Duration: " << DUR-reset << endl;
		if(SOFT_RESET)
			outFile << "Window Size: " << windowSize << endl;
		outFile << "Total Messages Done: " << messages_done << endl; 
		if(fWIRELESS)
		{
			outFile << "Total Wireless Messages Done: " << wireless_done << endl;
			outFile << "Total Wireless Usage: " << wireless_usage << endl;
		}
		if (top_type == SUPERS)
		{
			if (GHOST) outFile << "Throughput: " << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << endl;
			else outFile << "Throughput: " << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << endl;
		}
		else
		{
			if (GHOST) outFile << "Throughput: " << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << endl;
			else outFile << "Throughput: " << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << endl;
		}
		outFile << "Avg. Message Latency: " << (float) total_latency/messages_done << endl;
		outFile << "Avg. Network Latency: " << (float) network_latency/messages_done << endl;
		outFile << "Flits Injected: " << flitsInjected << endl;
		outFile << endl;

		int check_link_flit_counter=0;
		//start of debugging stuff
		outFile << "Link Flit Count: " << endl;
		for(int temp0 = 0; temp0 < numNodes*numPorts; temp0++)
		{
			outFile << link_flit_counter[temp0] << " ";
			check_link_flit_counter+=link_flit_counter[temp0];
		}
		cout<<"\nLink flit count verification: "<<check_link_flit_counter<<endl;
		outFile<<"\nLink flit count verification: "<<check_link_flit_counter<<endl;

		for(int temp1 = 0; temp1 < NUM_IPS; temp1++)
		{
			wireless << wirelessUsage[temp1] << endl;
			for(int temp2 = temp1; temp2 < NUM_IPS; temp2++)
			{
				if(temp1 == temp2)
					flitInjected << flitsPerLink[temp1][temp2] << endl;
				else
					linkUsage << (flitsPerLink[temp1][temp2] + flitsPerLink[temp2][temp1]) << endl;
			}
		}

		outFile << endl;
		outFile << "Node Flit Count: " << endl;
		for(int temp1 = 0; temp1 < numNodes; temp1++)
			outFile << node_flit_counter[temp1] << " ";
		outFile << endl;
		outFile << "Total Hop Count: " << flit_hop_count << endl;
		outFile << "Total Packet Count: " << total_flit_count << endl;
		outFile << endl << endl;
		//end of debugging stuff
		
		//Start of new energy Calculations Karthi

		//Automated Flit counting
		int flits_between_switches[64][64]={0};
		int temp_flit_count=0;
		int temp_flit_count1=0;
		int temp_link_flit_count;
		int x,y;

		//cout<<"Ports per switch: "<<numPorts<<endl;
		for(int temp0 = 0; temp0 < numNodes*numPorts; temp0++)
		{
			if((temp0/numPorts)<numIps)
			{
				x=temp0/numPorts;
			}
			else
			{
				x=(temp0/numPorts)-numIps;
			}
			if((ports[temp0].next/numPorts)<numIps)
			{
				y=ports[temp0].next/numPorts;
			}
			else
			{
				y=(ports[temp0].next/numPorts)-numIps;
			}

			if(!(x==0 &&y==0))
			{
				if(ports[temp0].next==0)
				{
					continue;
				}
			}
			if(flits_between_switches[x][y]!=0)
			{
				flits_between_switches[x][y]+=link_flit_counter[temp0];
			}
			else
			{
				flits_between_switches[x][y]=link_flit_counter[temp0];
			}
		//	cout<<"Temp0: "<<temp0<<" switch1: "<<x<<" switch2: "<<y<<" port flit count: "<<link_flit_counter[temp0]<<endl; 
	 }

		//Automating work sheet
		
		int new_wireline_flit_count=0;
		int new_wireless_flit_count=0;
		float new_total_node_energy=0;
		float new_node_energy[128]={0};
		int flits_through_switches[64]={0};
		int total_flits_through_switches=0;
		int	flits_injected_calc[64]={0};

		int wireline_flits_between_switches[64][64]={0};
		int wireless_flits_through_switches[64]={0};

		int wireline_flit_count=0;
		float wireline_energy=0;
		float wireless_energy=0;
		float total_node_energy=0;
		float node_energy[128]={0};
		int node_ports;
		int check1=0;
		int check2=0;
		
		for(int a=0;a<numSwitches;a++)
		{
			//cout<<"wireless node value: node "<<a<<"wireless value:"<<wireless_node[a]<<endl;

			for(int b=0;b<numSwitches;b++)
			{				
				if(a!=b)
				{
					if(!fMESH && wireless_node[a]>0 && wireless_node[b]>0 && (wireless_node[a]==wireless_node[b] || wireless_node[a] ==4 || wireless_node[b]==4))
					{				
						new_wireless_flit_count+=flits_between_switches[a][b];
						wireless_flits_through_switches[a]+=flits_between_switches[a][b];
						flits_through_switches[b]+=flits_between_switches[a][b];
						flits_through_switches[a]+=flits_between_switches[a][b];
					}
					else
					{
						check1+=flits_between_switches[a][b];						
						new_wireline_flit_count+=flits_between_switches[a][b];
						wireline_flits_between_switches[a][b]=flits_between_switches[a][b];
						flits_through_switches[b]+=flits_between_switches[a][b];
						flits_through_switches[a]+=flits_between_switches[a][b];
					}					
				}
				else if(a==b)
				{
					check2+=flits_between_switches[a][b];
					flits_through_switches[a]+=flits_between_switches[a][b];
				}				
			}
		}
		outFile<<"check1: "<< check1<<"check2: "<<check2;

		//wireline link energy calculation
		for(int a=0;a<64;a++)
		{
			for(int b=0;b<64;b++)
			{
				wireline_energy+=link_cartesian_distance[a][b]*wireline_flits_between_switches[a][b]*8.5E-12;
			}
		}

		
		//calcuating switch energy
		for(int a=0;a<numSwitches;a++)
		{
			total_flits_through_switches+=flits_through_switches[a];

			 if(!fMESH)
			 {	
				 node_ports=2;
				 node_ports+=tokenPortStart[a]-(a+numSwitches)*numPorts;
#if 0
				 if(wireless_node[a]>0 && wireless_node[a]<4) //adding wireless ports
				 {
				 	node_ports++;
				 }
				 else if(wireless_node[a]==4)//adding wireless ports to gateway
				 {
					node_ports+=3;
				 }
#endif 
			 }
			 else
			 {
				node_ports=7;
				if(a/8==0 ||a/8==7)
					node_ports=node_ports-1;
				if(a%8==0 ||a%8==7)
				node_ports=node_ports-1;
			 }
			
			 new_node_energy[a]=flits_through_switches[a]*node_ports*2.5817E-12;
			 new_total_node_energy+=new_node_energy[a];
		}

		//calcuating wireless energy
		for(int a=0;a<numSwitches;a++)
		{
			if(wireless_flits_through_switches[a]>0)
				cout<<"The wireless flitcount: form node: "<<a<<" count: "<<wireless_flits_through_switches[a]<<endl;
			wireless_energy+=wireless_flits_through_switches[a]*1.95E-12*32;
		}	

		cout<<"\n\nKarthi Energy: \ntotal flits through switches: "<<total_flits_through_switches<<endl;
		cout<<"Wireline flit count:"<<new_wireline_flit_count<<endl;
		cout<<"Wireless flit count:"<<new_wireless_flit_count<<endl;
		cout<<"total Switch energy: "<< new_total_node_energy<<endl;
		cout<<"total wireline energy: "<<wireline_energy<<endl;
		cout<<"total wireless energy: "<<wireless_energy<<endl;
		cout<<"total  energy: "<< new_total_node_energy+wireless_energy+wireline_energy<<endl;
		cout<<"Average energy per message done:"<< (double)(new_total_node_energy+wireless_energy+wireline_energy)/(double)messages_done<<endl;
		cout<<"Karthi Energy Calculations end\n\n\n\n"<<endl;

		outFile<<"Karthi Energy Calculations start\n\n\n\n"<<endl;
		outFile<<"total flits through switches: "<<  total_flits_through_switches<<endl;
		outFile<<"Wireline flit count:"<<new_wireline_flit_count<<endl;
		outFile<<"Wireless flit count:"<<new_wireless_flit_count<<endl;
		outFile<<"total Switch energy: "<< new_total_node_energy<<endl;
		outFile<<"total wireline energy: "<<wireline_energy<<endl;
		outFile<<"total wireless energy: "<<wireless_energy<<endl;
		outFile<<"total  energy: "<< new_total_node_energy+wireless_energy+wireline_energy<<endl;
		outFile<<"Average energy per message done:"<< (double)(new_total_node_energy+wireless_energy+wireline_energy)/(double)messages_done<<endl;
		outFile<<"Karthi Energy Calculations end\n\n\n\n"<<endl;

		resultFile<<benchmark<<"\t"<<(float) network_latency/messages_done<<"\t"<<messages_done<<"\t"<<wireless_done<<"\t"<<new_total_node_energy<<"\t"<<wireless_energy+wireline_energy<<"\t"<<new_total_node_energy+wireless_energy+wireline_energy<<"\t"<<(double)(new_total_node_energy+wireless_energy+wireline_energy)/(double)messages_done<<endl;

		//end of karthi energy calc stuff

		//outFile << "Avg. Queue Size: " << (float) avg_queue_size/(numIpsUsed*(DUR-reset)) << endl;
		//outFile << "Average Number of Iterations per cycle: " << (float) counter/(DUR-reset) << endl;
		outFile << "Internode Flit Total: " << internode_total << endl;
		outFile << "Intranode Data Flit Total: " << intranode_data_total << endl;
		outFile << "Intranode Header Flit Total: " << intranode_header_total << endl;
		outFile << "Internode Local Flit Total: " << internode_local << endl;
		outFile << "Internode Mid Flit Total: " << internode_mid << endl;
		outFile << "Internode Long Flit Total: " << internode_long << endl;
		outFile << "z-Dimension Internode Flit Total: " << internode_z << endl;
		//outFile << "Intranode Header Flit Total/DUR: " << (float)intranode_header_total/((DUR-reset)) << endl;
		//outFile << "Intranode Data Flit Total/DUR: " << (float)intranode_data_total/((DUR-reset)) << endl;
		//outFile << "Internode Flit Total/DUR: " << (float)internode_total/((DUR-reset)) << endl;
		outFile << "Average Energy per Message: " << total_energy/(1000*messages_done) << " nJ" << endl; 
		outFile << "Average Total Energy per Cycle: " << total_energy/(1000*(DUR-reset)) << " nJ" << endl; 
		outFile << "Total Energy: " << total_energy/(DUR-reset) << " pJ" << endl;
		outFile << "Header Energy: " << header_energy/(DUR-reset) << " pJ" << endl;
		outFile << "Data Energy: " << data_energy/(DUR-reset) << " pJ" << endl;
		outFile << "Internode Energy: " << internode_energy/(DUR-reset) << " pJ" << endl << endl;

		if (top_type!=OCTOM256 && top_type!=OCTOM){
			if (cycles>DUR+1) 
				if (GHOST) loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";" << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl-1) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";OVERLOAD" <<  endl;
				else loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";" << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";OVERLOAD" <<  endl;
			else
				if (top_type==HBUS) {
					if (GHOST) loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl-1) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
						<< ";" << (float)local_bus_tot*.151/((DUR-reset)) << ";" << (float)far_bus_tot*.223/((DUR-reset)) << ";" << (float)(local_bus_tot*.151+far_bus_tot*.223)/(DUR-reset) <<  endl;
					else loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
						<< ";" << (float)local_bus_tot*.151/((DUR-reset)) << ";" << (float)far_bus_tot*.223/((DUR-reset)) << ";" << (float)(local_bus_tot*.151+far_bus_tot*.223)/(DUR-reset) <<  endl;
				}
				else {
					if (GHOST) loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl-1) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
						<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << endl;
					else loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
						<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << endl;
				}

		}
		else {
			if (cycles>DUR+1) 
				if (GHOST) loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl-1) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";" << (float)internode_local/(DUR-reset) << ";" << (float)internode_mid/(DUR-reset) << ";" << (float)internode_long/(DUR-reset) << ";OVERLOAD" <<  endl;
				else loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl) << ";" << traffic << ";" << local << ";" << top_type << ";" << load << ";" << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";" << (float)internode_local/(DUR-reset) << ";" << (float)internode_mid/(DUR-reset) << ";" << (float)internode_long/(DUR-reset) << ";OVERLOAD" <<  endl;
			else 
				if (GHOST) loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl-1) << ";" << traffic << ";" << local << ";" << top_type << ";" <<load << ";" << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";" << (float)internode_local/(DUR-reset) << ";" << (float)internode_mid/(DUR-reset) << ";" << (float)internode_long/(DUR-reset) <<  endl;
				else loadFile << (float)tr_msgs/(DUR*(numIps/msgl)) <<";" << DUR << ";" << tr_msgs << ";"  << messages_done << ";" << numVirts << ";" << queueSize << ";" << (msgl) << ";" << traffic << ";" << local << ";" << top_type << ";" <<load << ";" << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << ";" << (float) total_latency/messages_done
					<< ";" << (float)intranode_header_total/((DUR-reset)) << ";" << (float)intranode_data_total/((DUR-reset)) << ";" << (float)internode_total/((DUR-reset)) << ";" << (float)internode_local/(DUR-reset) << ";" << (float)internode_mid/(DUR-reset) << ";" << (float)internode_long/(DUR-reset) <<  endl;
		}



		for (int m=0; m < maxLatency+1; m++)
			latencyHistogramFile << m << ";" << latency_histogram[m] << endl;
		for (int m=0; m < DUR/100; m++)
			arrivalHistogramFile << m << ";" << arrival_histogram[m] << endl;

		cout << "\n\n****************\nTesting Duration: " << DUR-reset << endl;
		cout << "Total Messages Done: " << messages_done << endl; 

		if (top_type == SUPERS)
		{
			if (GHOST)	cout << "Throughput: " << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << endl;
			else cout << "Throughput: " << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << endl;
		}
		else
		{
			if (GHOST)	cout << "Throughput: " << (float) messages_done*(msgl-1)/((DUR-reset)*numIpsUsed) << endl;
			else cout << "Throughput: " << (float) messages_done*(msgl)/((DUR-reset)*numIpsUsed) << endl;
		}
		averageLatency2[z] = (double) total_latency/messages_done;
		averageLatency[z] = (double) network_latency/messages_done;
		if((double) network_latency/messages_done > maxLatency2)
			maxLatency2 = (double) network_latency/messages_done;
		cout << "Avg. Message Latency: " << (float) total_latency/messages_done << endl;
		cout << "Avg. Network Latency: " << (float) network_latency/messages_done << endl;
		cout << "Avg. Queue Size: " << (float) avg_queue_size/(numIpsUsed*(DUR-reset)) << endl;
		cout << "Avg. Active Messages / cycle: " << (float) activeMessages/(DUR-reset) << endl;
		cout << "Average Number of Iterations per cycle: " << (float) (counter-1)/(DUR-reset) << endl;
		cout << "Flits Injected: " << flitsInjected << endl;
		cout << "Flits Consumed: " << flitsConsumed << endl;
		cout << "Flits Moved: " << flitsMoved << endl;
		cout << "Intranode Header Flit Total: " << intranode_header_total << endl;
		cout << "Intranode Data Flit Total: " << intranode_data_total << endl;
		cout << "Internode Flit Total: " << internode_total << endl;
		cout << "z-Dimension Internode Flit Total: " << internode_z << endl;
		cout << "Intranode Header Flit Total/DUR: " << (float)intranode_header_total/((DUR-reset)) << endl;
		cout << "Intranode Data Flit Total/DUR: " << (float)intranode_data_total/((DUR-reset)) << endl;
		cout << "Internode Flit Total/DUR: " << (float)internode_total/((DUR-reset)) << endl;
		if (top_type==HBUS) cout << "Local Energy/cycle (nJ): " << (float)local_bus_tot*0.151 << endl;
		if (top_type==HBUS) cout << "Non-local Energy/cycle (nJ): " << (float)far_bus_tot*.223 << endl;;
		if (top_type==HBUS) cout << "Total Energy/cycle (nJ): " << (float)local_bus_tot*0.151 + far_bus_tot*.223 << endl;
		if (select_function==3) cout << "0 - Priority Avg. Latency: " << (float) total_latency0/messages_done0 << endl;
		if (select_function==3) cout << "1 - Priority Avg. Latency: " << (float) total_latency1/messages_done1 << endl;
		if (select_function==3) cout << "2 - Priority Avg. Latency: " << (float) total_latency2/messages_done2 << endl;
		if (select_function==3) cout << "3 - Priority Avg. Latency: " << (float) total_latency3/messages_done3 << endl;


		if (top_type==OCTOM256 || top_type==OCTOM || top_type==KARY || top_type==BFT){
			cout << "Internode Local Flit Total: " << internode_local << endl;
			cout << "Internode Mid Flit Total: " << internode_mid << endl;
			cout << "Internode Long Flit Total: " << internode_long << endl;
			//cout << "Internode Local Flit Total/DUR: " << (float)internode_local/((DUR-reset)) << endl;
			//cout << "Internode Mid Flit Total/DUR: " << (float)internode_mid/((DUR-reset)) << endl;
			//cout << "Internode Long Flit Total/DUR: " << (float)internode_long/((DUR-reset)) << endl;

		}

		cout << "Average Energy per Message: " << total_energy/(1000*messages_done) << " nJ" << endl; 
		cout << "Average Total Energy per Cycle: " << total_energy/(1000*(DUR-reset)) << " nJ" << endl; 
		cout << "Total Energy: " << total_energy/(DUR-reset) << " pJ" << endl;
		cout << "Header Energy: " << header_energy/(DUR-reset) << " pJ" << endl;
		cout << "Data Energy: " << data_energy/(DUR-reset) << " pJ" << endl;
		cout << "Internode Energy: " << internode_energy/(DUR-reset) << " pJ" << endl << endl;

		cout << "Elapsed Time (mins:sec) " << (time(NULL)-initialTime)/60 << ":" << (time(NULL)-initialTime) -((time(NULL)-initialTime)/60)*60 << endl;
	}

	double totalLatency = 0.0;
	double totalLatency2 = 0.0;

	for(int z = 0; z < 100; z++)
	{
		totalLatency += averageLatency[z];
		totalLatency2 += averageLatency2[z];
	}

	cout << endl << endl << "Average Network Latency over 100 runs: " << (double) totalLatency/100 << endl;
		cout << endl << endl << "Average Total Latency over 100 runs: " << (double) totalLatency2/100 << endl;
		cout << endl << endl << "Max Latency: " << maxLatency2 << endl;
	outFile << endl << endl << "Messages_done: " << messages_done << endl << "Active messages: " << numActiveMsgs << endl << "Latency: " << (float) total_latency/messages_done << endl << endl;

	outFile << endl << endl;

	for(int pcount = 0; pcount < numPorts*numNodes; pcount++)
	{
		outFile << "ports[" << pcount << "].next = " << ports[pcount].next << endl;
	}


	for ( int q = 0 ; q < numPorts*numNodes; q++){
		free (ports[q].i_buff);
		free (ports[q].o_buff);
	}

	for (int n=0; n < numIps; n++){
		free (ips[n].consume);
		free (ips[n].generate);
		free (ips[n].queue);
	}
	if(fALASH)
			{
	for(int i = 0; i < numNodes; i++)
	{
		for(int j = 0; j < numNodes; j++)
		{
			
				if(connection[i][j] > -1)
				{
					linkuseFile << i << "\t" << j << "\t" << (communicationPerLink[i][j][0] + communicationPerLink[i][j][1] + communicationPerLink[i][j][2] + communicationPerLink[i][j][3]) << endl;
				}
			
		}
	}
	}
	 

	outFile.close();
	messagesFile.close();
	linkuseFile.close();
	latencyHistogramFile.close();
	arrivalHistogramFile.close();
	adjacentcyListFile.close();
	portsFile.close();
	gateFile.close();
	loadFile.close();
	octoOut.close();

	// system("pause");	// yuchen: no pause system call for debian

	freeRoutingTables();


	free (latency_histogram);
	free (arrival_histogram);
	free (ports);
	free (ips);
	free (to_internode_move_ports);
	free (to_internode_move_oldports);
	free (to_internode_move_flits);
	free (to_internode_move_virts);
	free (to_internode_move_oldvirts);
	free (to_intranode_move_ports);
	free (to_intranode_move_oldports);
	free (to_intranode_move_flits);
	free (to_intranode_move_virts);
	free (to_intranode_move_oldvirts);
	free (vary);
	free (tempAddr);
	free (firstCollision);

	for (int a =0; a < maxMessage; a++){
		free (msgs[a].source);
		free (msgs[a].dest);
		free (msgs[a].path);
		free (msgs[a].vpath);
	}
	free (msgs);

	if(top_type == SUPERS)
	{
		for(maxLatency = 0; maxLatency < numNodes; maxLatency++)
		{
			free(connection[maxLatency]);
			free(lookup[maxLatency]);
		}
		free(connection);
		free(lookup);
		free(path);
		free(superpath);
	}

	return 0;
}

int ss_route_mesh(int m)
{
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;

	nd = pt/numPorts;		//check this
	get_cube_rel_addr(nd);  

	//tempAddr should be up to date

	// Dimension ordered routing, no wrap around links used
	// check if reached destination
	port=0;
	for (int d=0; d < dimensions; d++)
	{
		// cycle through dimensions, check if at correct address
		if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d] != tempAddr[d])
		{
			if (msgs[ports[pt].i_buff[buff] % maxMessage].dest[d] > tempAddr[d])
			{
				port = nd*numPorts+2+2*d; // route to higher nodes
			}
			else
			{
				port = nd*numPorts+1+2*d; // route to lower nodes
			}
			d = dimensions+1;	// exit routing loop
		}
	}

	if (port==0)
	{
		port= nd*numPorts;	// destination reached
	}

	return port;		// includes node
}

int ss_route_bft(int m)
{
	return 0;

}

int ss_route_rand(int m)
{
	int v = msgs[m].vpath[msgs[m].path_length-1];	// current virt, buffer always 0
	int pt = msgs[m].path[msgs[m].path_length-1];	// current port (node included)
	int buff = v*bufferDepth;
	int port, nd;
	int i;
	int current_switch = -1;
	int destination_switch = -1;
	int next_switch = -1;
	int previous_switch = -1;

	port = ports[pt].i_buff[buff] % maxMessage;

	nd = pt/numPorts;		//check this

	port=0;

	if (m!=ports[pt].i_buff[buff] % maxMessage) 
		cout << "ERROR in Rand route at cycle: " << cycles << ", msg: " << m << ", Port: "<< pt << endl;
	if(msgs[m].path_length > 132)
		cout << "ERROR in Rand route at cycle: " << cycles << ", msg: " << m << ", Port: "<< pt << endl;

	if(m == 368)
	{
		if(msgs[m].source[0] == 51)
		{
			if(msgs[m].dest[0] == 10)
			{
				m = m;
			}
		}
	}


	current_switch = (nd - numIps);
	destination_switch = msgs[m].dest[0];
	previous_switch = ((msgs[m].path[(msgs[m].path_length-2)]/numPorts)-numIps);
	if((nd-numIps) == msgs[m].dest[0])
	{
		port = 0;
	}
	else if(nd != msgs[m].dest[0])
	{
		if(fALASH && !fWIRELESS)
		{
			double best_commDens = 100000;
			double commDens = 0;
			int bestLayer = -1;
			int bestPath = -1;
			int previousPath = msgs[m].path_history[msgs[m].path_length-1];
			int previousLayer = msgs[m].vpath[msgs[m].path_length-1];

			current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
			destination_switch = msgs[m].dest[0];

			for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
			{
				if(MultiPathLength[current_switch][destination_switch][0] == MultiPathLength[current_switch][destination_switch][pathnumber])
				{
					for(int j = numLayers-1; j >= 0 ; j--)
					{
						commDens = 0;
						if(pathAllocLayer[current_switch][destination_switch][pathnumber][j] == 1 && (msgs[m].vpath[msgs[m].path_length-1] == j || msgs[m].layer_history[j] == 0))
						{
							for (i = 1; i < MultiPathLength[current_switch][destination_switch][pathnumber]-2; i++)
							{
								commDens += communication_density[MultiPathMsg[current_switch][destination_switch][pathnumber][i]][MultiPathMsg[current_switch][destination_switch][pathnumber][i+1]][j];
							}
							if(bestLayer == -1 || (commDens) < best_commDens)
							{
								bestLayer = j;
								best_commDens = commDens;
								bestPath = pathnumber;
							}
						}
					}
				}
			}
			if(bestLayer != -1)
			{
				msgs[m].layer = bestLayer;
				//msgs[m].source[0] = current_switch;
				msgs[m].pathNum = bestPath;
				next_switch = MultiPathMsg[current_switch][destination_switch][bestPath][2];
			}
			else
			{
				current_switch = msgs[m].path[msgs[m].path_length-1];
				for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum]; i++)
				{
					if(current_switch/numPorts == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i])
						break;
				}
				if(i == MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum])
					printf("There has been an error in routing %d\n", m);
				else if( i < (MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum] - 1))
					next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i+1];
			}
		}
		if(fALASH && fWIRELESS)
		{
			current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
			destination_switch = msgs[m].dest[0];

			if(-1 == MultiPathLength[current_switch][msgs[m].dest[0]][wirelessPathNum])
				msgs[m].rerout = true;

			if( msgs[m].rerout == false)
			{
				current_switch = msgs[m].path[msgs[m].path_length-1]/numPorts;
				for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][wirelessPathNum]; i++)
				{
					if(current_switch == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][wirelessPathNum][i])
						break;
				}
				next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][wirelessPathNum][i+1];

		//distributed_control MAC

				if(DC_MAC)
				{
					switch(connections[current_switch][next_switch][0])
					{
					case '1':

					if(token1 != current_switch)
					{
						//cout<<"wireless checking: Cycles "<<cycles<<" current : "<<current_switch<<" next_switch: "<<next_switch<<" channel: "<<connections[current_switch][next_switch][0]<<endl;
						//cout<<"Token1: "<<token1<<endl;
						if(free_token[0]==true && msgs[m].wait == -1)
						{
							msgs[m].wait =1;
							net_possible_wireless_tx++;
							token_request[current_switch][0]=true;
							request_count[0]++;
							//cout<<" cycles : "<<cycles<<"Request count :"<<request_count[0]<<endl;
							//request generation
						}

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
							rerouted++;
						}
						else
						{
							msgs[m].wait--;
							return -1;
						}
					}
					else
					{
						//count_possible_wireless_tx++;
						//cout<<"count me in"<<endl;
						msgs[m].wait = -1;
					}
					break;

				case '2':
					//net_possible_wireless_tx++;

					if(token2 != current_switch)
					{
						if(free_token[1]==true && msgs[m].wait == -1)
						{
							msgs[m].wait =1;
							net_possible_wireless_tx++;
							token_request[current_switch][1]=true;
							request_count[1]++;
							//request generation
						}

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
							rerouted++;
						}
						else
						{

							msgs[m].wait--;
							return -1;
						}
					}
					else
					{
						//count_possible_wireless_tx++;
						//cout<<"count me in"<<endl;
						msgs[m].wait = -1;
					}
					break;
				case '3':
					//net_possible_wireless_tx++;
					if(token3 != current_switch)
					{
						if(free_token[2]==true && msgs[m].wait == -1)
						{
							msgs[m].wait =1;
							net_possible_wireless_tx++;
							token_request[current_switch][2]=true;
							request_count[2]++;
							//request generation
						}

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
							rerouted++;
						}
						else
						{
							msgs[m].wait--;
							return -1;
						}
					}
					else
					{
						//count_possible_wireless_tx++;
						//cout<<"count me in"<<endl;
						msgs[m].wait = -1;
					}
					break;
				default:
					break;
				}
			}
				
				//token mac
			if(TOKEN_MAC)
			{
				switch(connections[current_switch][next_switch][0])
				{
				case '1':
					count_possible_wireless_tx++;
					if(token1 != current_switch)
					{
						if(msgs[m].wait == -1)
							msgs[m].wait = wiWaitThreshold;

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
						}
						else
						{
							msgs[m].wait--;
							return -1;
						}
					}
					else
						msgs[m].wait = -1;
					break;
				case '2':
					count_possible_wireless_tx++;
					if(token2 != current_switch)
					{
						if(msgs[m].wait == -1)
							msgs[m].wait = wiWaitThreshold;

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
						}
						else
						{
							msgs[m].wait--;
							return -1;
						}
					}
					else
						msgs[m].wait = -1;
					break;
				case '3':
					count_possible_wireless_tx++;
					if(token3 != current_switch)
					{
						if(msgs[m].wait == -1)
							msgs[m].wait = wiWaitThreshold;

						if(msgs[m].wait == 0)
						{
							msgs[m].wait = -1;
							msgs[m].rerout = true;
						}
						else
						{
							msgs[m].wait--;
							return -1;
						}
					}
					else
						msgs[m].wait = -1;
					break;
				default:
					break;
				}
				}
			}

			if(msgs[m].rerout == false)
			{
				double best_commDens = 100000;
				double commDens = 0;
				int bestLayer = -1;
				int bestPath = -1;
				int previousPath = msgs[m].path_history[msgs[m].path_length-1];
				int previousLayer = msgs[m].vpath[msgs[m].path_length-1];
				int prev_switch = msgs[m].path[msgs[m].path_length-2]/numPorts - numIps;

				if(prev_switch < 0)
					prev_switch += numIps;

				current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
				destination_switch = msgs[m].dest[0];

				for(int pathnumber = (maxPaths - 1); pathnumber >= 0; pathnumber--)
				{
					if(-1 != MultiPathLength[current_switch][destination_switch][pathnumber])
					{
						for(int j = numLayers-1; j >= 0 ; j--)
						{
							bool pastHistory = false;

							for(int i = 0; i < maxPaths; i++)
							{
								if(pathAllocLayer[prev_switch][destination_switch][i][j] ==  1 && MultiPathMsg[prev_switch][destination_switch][i][2] == (current_switch+numIps))
									pastHistory = true;
							}
							commDens = 0;
							if(pathAllocLayer[current_switch][destination_switch][pathnumber][j] == 1 && (msgs[m].vpath[msgs[m].path_length-1] == j || msgs[m].layer_history[j] == 0 || pastHistory))
							{
								for (i = 1; i < MultiPathLength[current_switch][destination_switch][pathnumber]-2; i++)
								{
									commDens += communication_density[MultiPathMsg[current_switch][destination_switch][pathnumber][i]][MultiPathMsg[current_switch][destination_switch][pathnumber][i+1]][j];
								}
								if(bestLayer == -1 || (commDens) < best_commDens)
								{
									bool allEmpty = true;
									for (int x =0; x < bufferDepth; x ++){
										if (ports[msgs[m].path[msgs[m].path_length-1]].o_buff[j*bufferDepth+x]!=0){
											allEmpty=false;
											x = bufferDepth+10;
										}
									}
									if(allEmpty)
									{
										bestLayer = j;
										best_commDens = commDens;
										bestPath = pathnumber;
									}
								}
							}
						}
					}
				}
				if(bestLayer != -1)
				{
					msgs[m].layer = bestLayer;
					//msgs[m].source[0] = current_switch;
					msgs[m].pathNum = bestPath;
					next_switch = MultiPathMsg[current_switch][destination_switch][bestPath][2];
				}
				else
				{
					current_switch = msgs[m].path[msgs[m].path_length-1];
					for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum]; i++)
					{
						if(current_switch/numPorts == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i])
							break;
					}
					if(i == MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum])
						printf("There has been an error in routing %d\n", m);
					else if( i < (MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum] - 1))
						next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i+1];
				}
			}

			if(msgs[m].rerout == true)
			{
				double best_commDens = -1;
				double commDens = 0;
				int bestLayer = -1;
				int bestPath = -1;
				int prev_switch = msgs[m].path[msgs[m].path_length-2]/numPorts - numIps;

				if(prev_switch < 0)
					prev_switch += numIps;
				current_switch = (msgs[m].path[msgs[m].path_length-1]/numPorts) - numIps;
				if(current_switch < 0)
					current_switch += numIps;
				for(int pathnumber = (maxPaths - 1); pathnumber >= 0; pathnumber--)
				{
					if(pathnumber != wirelessPathNum)
					{
						for(int j = numLayers-1; j >= 0 ; j--)
						{
							bool pastHistory = false;
							for(int i = 0; i < maxPaths; i++)
							{
								if(pathAllocLayer[prev_switch][destination_switch][i][j] ==  1 && MultiPathMsg[prev_switch][destination_switch][i][2] == (current_switch+numIps))
									pastHistory = true;
							}
							commDens = 0;
							if(pathAllocLayer[current_switch][destination_switch][pathnumber][j] == 1 && (msgs[m].vpath[msgs[m].path_length-1] == j || msgs[m].layer_history[j] == 0))
							{
								for (int i = 1; i < MultiPathLength[current_switch][destination_switch][pathnumber]-2; i++)
								{
									commDens += communication_density[MultiPathMsg[current_switch][destination_switch][pathnumber][i]][MultiPathMsg[current_switch][destination_switch][pathnumber][i+1]][j];
								}
								if(bestLayer == -1 || (commDens) < best_commDens)
								{
									bestLayer = j;
									best_commDens = commDens;
									bestPath = pathnumber;
								}
							}
						}
					}
				}
				if(bestLayer != -1)// && msgs[m].rerout == false)
				{
					msgs[m].layer = bestLayer;
					msgs[m].source[0] = current_switch;
					msgs[m].pathNum = bestPath;
					next_switch = MultiPathMsg[current_switch][destination_switch][bestPath][2];
				}

				else
				{
					current_switch = msgs[m].path[msgs[m].path_length-1];
					for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum]; i++)
					{
						if(current_switch/numPorts == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i])
							break;
					}
					if(i == MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum])
						printf("There has been an error in routing %d\n", m);
					else if( i < (MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum] - 1))
						next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i+1];
				}
			}
		}
		if(fMPLASH || fLASH)
		{
			current_switch = msgs[m].path[msgs[m].path_length-1];
			for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum]; i++)
			{
				if(current_switch/numPorts == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i])
					break;
			}
			if(i == MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum])
				printf("There has been an error in routing %d\n", m);
			else if( i < (MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum] - 1))
				next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i+1];
			if(fWIRELESS)
			{
				if(connections[current_switch/numPorts][next_switch][0] != 'D')
				{
					bool noToken = false;
					switch(connections[current_switch/numPorts][next_switch][0])
					{
					case '1':
						if(token1 != current_switch/numPorts)
						{
							noToken = true;
						}
						break;
					case '2':
						if(token2 != current_switch/numPorts)
						{
							noToken = true;
						}
						break;
					case '3':
						if(token3 != current_switch/numPorts)
						{
							noToken = true;

						}
						break;
					}
					if(noToken)
					{
						int layer = pathLayer[(current_switch/numPorts-numIps)][msgs[m].dest[0]][0];
						bool allEmpty = true;
						int nextPort = connection[next_switch][nd];
						for(i = 0; i < bufferDepth; i++)
						{
							if(ports[nextPort].o_buff[layer*bufferDepth+i] != 0)
								allEmpty = false;
						}
						if(!allEmpty)
							return -1;
						else
						{
							msgs[m].pathNum = 0;
							msgs[m].sourceOrig = msgs[m].source[0];
							msgs[m].source[0] = current_switch/numPorts-numIps;
							msgs[m].layer = pathLayer[msgs[m].source[0]][msgs[m].dest[0]][0];
							msgs[m].rerout = true;
							rerouted++;
						}

					}
					if(msgs[m].rerout == true)
					{
						for(i =0; i < MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum]; i++)
						{
							if(current_switch/numPorts == MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i])
								break;
						}
						if(i == MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum])
							printf("There has been an error in routing %d\n", m);
						else if( i < (MultiPathLength[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum] - 1))
							next_switch = MultiPathMsg[msgs[m].source[0]][msgs[m].dest[0]][msgs[m].pathNum][i+1];
					}
				}
			}
		}
		if(fMROOTS)
		{
			if(GLOBAL)
			{
				next_switch = globalThermalRerout(current_switch, msgs[m].source[0], msgs[m].dest[0], &msgs[m].global_pathNumber, msgs[m].priority);

				if(next_switch == -2)
				{
					msgs[m].source[0] = current_switch;
					msgs[m].global_pathNumber = -2;
					next_switch = globalThermalRerout(current_switch, msgs[m].source[0], msgs[m].dest[0], &msgs[m].global_pathNumber, msgs[m].priority);

					if(next_switch == -2)
						cout << "ERROR in routing!" << endl << endl;
				}
			}
			else
			{
				next_switch = thermalRerout(current_switch, destination_switch, previous_switch, msgs[m].priority);

			}
			//next_switch = ss_route_mst(current_switch, destination_switch, 0);
			next_switch += numIps;
		}
		//if(next_switch == nd)
		//{
		//	port = 0;
		//}
		//else
		//{
		port = connection[next_switch][nd];
		//}
	}



	/*
	if (msgs[m].dest[0] != nd)
	{
	next_switch = lookup[nd][msgs[m].dest[0]];
	port = connection[next_switch][nd];

	}
	*/

	if (port==0)
	{
		port= nd*numPorts;	// destination reached
	}
	if (port < 0) //no connection making appropiate adjustments
	{
		port = nd*numPorts;
		msgs[m].dest[0] = nd;
		messages_done--;
	}

	return port;		
}

void minspantree(int length, int hop_count, int start, int current, int dest, int pathLength, bool wireless)
{
	int tcount = 0;
	int repeaters = 0;
	int node1_x = 0;
	int node1_y = 0;
	int node2_x = 0;
	int node2_y = 0;
	int temp1 = 0;
	int temp2 = 0;
	if (current == dest)
	{
		path[length] = current;
		if((fLASH || fALASH) && !wireless&& 0)
		{
			int i = 0;
			int j = maxPaths-2;
			int k = 0;
			int l = 0;
			int matching = 0;
			if(pathLength <= minPath)
			//if (hop_count <= min_hop_count)
			{
				minPath = pathLength;
				minlength = length;
				min_hop_count = hop_count;
				for(tcount = 0; tcount < numIps; tcount++)
				{
					superpath[tcount] = path[tcount];
				}
			}
		/*	while(MultiPathLength[start][dest][i] != 0 && MultiPathLength[start][dest][i] <= (length+1))
			{
				if(MultiPathLength[start][dest][maxPaths-1]  > 0 )
				{
					if(MultiPathLength[start][dest][i] == length+1)
					{
						matching = 0;
						//Check similarities in the path
						for (k = 0; k  < MultiPathLength[start][dest][i]; k++)
						{
							for(l = 0; l < length+1; l++)
							{
								if(MultiPathMsg[start][dest][i][k] == path[l])
									matching++;
							}
						}
						if(matching > MultiPathLength[start][dest][i]-2)
							return;
					}
				}
				i++;
				if(i == maxPaths)
					return;
			}

			while(j >= i)
			{
				for(k=0; k < maxPathLength; k++)
				{
					MultiPathMsg[start][dest][j+1][k] = MultiPathMsg[start][dest][j][k];
				}
				MultiPathLength[start][dest][j+1] = MultiPathLength[start][dest][j];
				j--;
			}
			for(k=0; k < maxPathLength; k++)
			{
				if(k < (length+1))
					MultiPathMsg[start][dest][i][k] = path[k];
				else
					MultiPathMsg[start][dest][i][k] = -1;
			}
			MultiPathLength[start][dest][i] = (length+1);*/

			if(pathLengthRepeaters[start][dest][1] == 0)
			{
				for (k = 0; k < maxPathLength; k++)
				{
					if(k < (length+1))
						MultiPathMsg[start][dest][1][k] = path[k];
					else
						MultiPathMsg[start][dest][1][k] = -1;
				}
				MultiPathLength[start][dest][1] = (length+1);
				pathLengthRepeaters[start][dest][1] = pathLength;
			}
			else if(pathLengthRepeaters[start][dest][1] > pathLength)
			{
				for(k = 0; k < maxPathLength; k++)
				{
					MultiPathMsg[start][dest][0][k] = MultiPathMsg[start][dest][1][k];
				}
				MultiPathLength[start][dest][0] = MultiPathLength[start][dest][1];
				for (k = 0; k < maxPathLength; k++)
				{
					if(k < (length+1))
						MultiPathMsg[start][dest][1][k] = path[k];
					else
						MultiPathMsg[start][dest][1][k] = -1;
				}
				MultiPathLength[start][dest][1] = (length+1);
				pathLengthRepeaters[start][dest][0] = pathLengthRepeaters[start][dest][1]; 
				pathLengthRepeaters[start][dest][1] = pathLength;
			}
			else if(pathLengthRepeaters[start][dest][0] > pathLength || pathLengthRepeaters[start][dest][0] == 0)
			{
				for (k = 0; k < maxPathLength; k++)
				{
					if(k < (length+1))
						MultiPathMsg[start][dest][0][k] = path[k];
					else
						MultiPathMsg[start][dest][0][k] = -1;
				}
				MultiPathLength[start][dest][0] = (length+1);
				pathLengthRepeaters[start][dest][0] = pathLength;
			}

			return;
		}
		else
		{
			if(pathLength > minPath)
			//if (hop_count > min_hop_count)
			{
				return; //too long, invalid path
			}
			else //same size or shorter path
			{
				//found dest, do stuff
				for(tcount = 0; tcount < numIps; tcount++)
				{
					superpath[tcount] = path[tcount];
				}
				minPath = pathLength;
				minlength = length;
				min_hop_count = hop_count;
				return;
			}
		}
	}
	else
	{
		if(fMPLASH)
		{
			if(min_hop_count < 6)
			{
				if (hop_count > min_hop_count+2)
					return; //length is too much
			}
			else
			{
				if(hop_count > min_hop_count+1)
					return;
			}
		}
		else
		{
			if(pathLength > minPath)
			//if(hop_count > min_hop_count)
				return;
		}
		if (length > 15)
		{
			return;
		}

		for(tcount = 0; tcount < length; tcount++)
		{
			if (current == path[tcount])
			{
				return; //came back around to itself, not valid path
			}
		}

		int colcount = 0;

		//not dest, shorter length, and new path so keep going

		if(connection[current][dest+NUM_IPS] != -1)
		{
			temp1 = current - NUM_IPS;
			temp2 = dest;
			node1_x = temp1 % ((int) sqrt(NUM_IPS));
			node1_y = temp1 / ((int) sqrt(NUM_IPS));
			node2_x = temp2 % ((int) sqrt(NUM_IPS));
			node2_y = temp2 / ((int) sqrt(NUM_IPS));
			repeaters = (int) ceil(sqrt(pow((node1_x-node2_x),2)+pow((node1_y-node2_y),2)));
			path[length] = current;
			minspantree(length+1, (hop_count + 1), start, (dest+NUM_IPS), dest, pathLength+repeaters, wireless); //lookupcycle[current][colcount]), start, colcount, dest);
		}
		for(colcount = 0; colcount < numNodes; colcount++)
		{
			if(colcount != (dest+NUM_IPS))
			{
				if (connection[current][colcount] != -1)
				{
					if(colcount < NUM_IPS)
					{
						if(colcount == dest)
						{
							path[length] = current;
							minspantree(length+1, (hop_count + 1), start, colcount, dest, pathLength, wireless);
						}
					}
					else if (current < NUM_IPS)
					{
						if(current == start)
						{
							path[length] = current;
							minspantree(length+1, (hop_count + 1), start, colcount, dest, pathLength, wireless);

						}
					}
					else
					{
						if(clusterMatrix[colcount-NUM_IPS] == clusterMatrix[start] || clusterMatrix[colcount-NUM_IPS] == clusterMatrix[dest] || !VFI)
						{
							if(connection[current][colcount] == 10)
							{
								bool alreadyWireless = false;
								for(int j = 0; j < length; j++)
								{
									if(connections[path[j]][path[j+1]][0] != 'D')
									{
										alreadyWireless = true;
									}
								}
								if(alreadyWireless)
									continue;
								repeaters = 1;
							}
							else
							{
								temp1 = current;
								temp2 = colcount;
								if(current >= NUM_IPS)
									temp1 -= NUM_IPS;
								if(colcount >= NUM_IPS)
									temp2 -= NUM_IPS;
								node1_x = temp1 % ((int) sqrt(NUM_IPS));
								node1_y = temp1 / ((int) sqrt(NUM_IPS));
								node2_x = temp2 % ((int) sqrt(NUM_IPS));
								node2_y = temp2 / ((int) sqrt(NUM_IPS));
								repeaters = (int) ceil(sqrt(pow((node1_x-node2_x),2)+pow((node1_y-node2_y),2)));
							}
							path[length] = current;
							minspantree(length+1, (hop_count + 1), start, colcount, dest, pathLength+repeaters+routerStages, wireless); //lookupcycle[current][colcount]), start, colcount, dest);
						}
					}
				}
			}
		}
	}

	return;
}

void make_connect_rand(int N, int S, int ks, int kmax, double alpha)
{
	//N = numIps, S = numSwitchs, ks = average connectivity, 
	//kmax = maximun number of connections per switch, alpha = connectivity parameter
	int traffic_help = 0;
	int maxmaxmax = 0;
	double distmaxhelp;
	int v = 0;
	int w = 0;

	int x;
	int y;
	int z;
	double t;
	int ohno = 0;

	int isGood = 0;

	int numberLinks = (ks * S) / 2;
	//int helper = S / 2;

	double minDistance = RAND_MAX;
	double distance = RAND_MAX;
	int tempNode;

	int** points;

	points = (int**) calloc(N + S, sizeof(int*));
	connection = (int**) calloc(N + S, sizeof(int*));
	lookupcycle = (int**) calloc(N + S, sizeof(int*));
	for(v = 0; v < N+S; v++)
	{
		points[v] = (int*) calloc(4, sizeof(int));
		connection[v] = (int*) calloc(N + S, sizeof(int));
		lookupcycle[v] = (int*) calloc(N + S, sizeof(int));
		for(w = 0; w < N+S; w++)
		{
			connection[v][w] = -1;
			lookupcycle[v][w] = 0;
		}

	}

	for(v = 0; v < N + S; v++)
	{
		for(w = 0; w < 4; w++)
		{
			points[v][w] = -1;
		}
	}

	/*
	for(v = 0; v < N + S; v++)
	{
	isGood = 0;

	while(!isGood)
	{
	isGood = 1;
	x = rand() % 9;
	y = rand() % 9;
	z = rand() % 9;

	for(w = 0; w < N + S; w++)
	{
	if (v == w)
	{
	}
	else
	{
	if( x == points[w][0] && y == points[w][1] && z == points[w][2])
	{
	isGood = 0;
	break;
	}
	}
	}
	}
	points[v][0] = x;
	points[v][1] = y;
	points[v][2] = z;
	}
	*/

	for(v = 0; v < N; v++)
	{
		if(N == 64)
		{
			points[v][0] = v / 8;
			points[v][1] = v % 8;
			points[v][2] = 0;
		}
		else
		{
			cout << "Error in random spots, need to write code for this!" << endl << endl;
		}
	}
	for(v = N; v < N+S; v++)
	{
		if(S == 64)
		{
			points[v][0] = (v-N) / 8;
			points[v][1] = (v-N) % 8;
			points[v][2] = 1;
		}
		else
		{
			cout << "Error in random spots, need to write code for this!" << endl << endl;
		}
	}

	for(v = 0; v < N; v++)
	{
		tempNode = N;
		minDistance = RAND_MAX;
		for(w = N; w < N + S; w++)
		{
			if (points[w][3] < (kmax - 2))
			{
				distance = sqrt((double) ((points[v][0] - points[w][0]) * (points[v][0] - points[w][0])) + ((points[v][1] - points[w][1]) * (points[v][1] - points[w][1])) + ((points[v][2] - points[w][2]) * (points[v][2] - points[w][2])));
				if (distance < minDistance)
				{
					minDistance = distance;
					tempNode = w;
				}
			}
		}
		//Connect Ip to Switch
		connection[tempNode][v] = 2;
		connection[v][tempNode] = 2;
		points[tempNode][3]++;
		points[v][3]++;

		if(traffic == 2)
		{
			for(w = 0; w < numHotspots; w++)
				if(v == hotspots[w])
					con_hotspots[w] = tempNode;
		}
		else if(traffic == 5)
		{
			for(w = 0; w < numTranspose; w++)
			{
				if(v == transpose[w][0])
					con_transpose[w][0] = tempNode;
				if(v == transpose[w][1])
					con_transpose[w][1] = tempNode;
			}

		}
	}

	int num_tries = 0;
	for(v = 0; v < numberLinks; v++)
	{
		num_tries = 0;
		traffic_help = 0;
		isGood = 0;
		while (!isGood)
		{
			x = rand() % S;
			x = x + N;
			ohno = points[x][3];
			if (ohno < (kmax-1))
			{
				isGood = 1;
			}
		}

		/*if(traffic_optim)
		{
		if(traffic == 2)
		{
		for(w = 0; w < numHotspots; w++)
		if(x == con_hotspots[w])
		traffic_help = 1;
		}
		else if(traffic == 5)
		{
		for(w = 0; w < numTranspose; w++)
		if(x == con_transpose[w][0])
		traffic_help = 1;
		else if(x == con_transpose[w][1])
		traffic_help = 1;
		}
		}*/

		isGood = 0;
		ohno = 0;
		while (!isGood)
		{
			num_tries++;
			/*if(!traffic_help && traffic_optim)
			{
			y = rand() % 100 + 1;

			if(y < hotPercent && traffic == 2)
			{
			y = rand() % 3;
			w = con_hotspots[y];
			if (points[w][3] < (kmax-1))
			{
			y = rand() % 100 + 1;

			t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
			t = pow(t, (-1 * alpha));
			z = t * 100 + 1;
			if (y < z)
			{
			isGood = 1;
			points[w][3]++;
			points[x][3]++;
			//Connect Switch to Switch
			connection[x][w] = 1;
			connection[w][x] = 1;
			cout << endl << "Made connection " << v << endl;
			break;
			}
			cout << ".";
			}
			}
			else
			{
			if (points[w][3] < (kmax-1))
			{
			y = rand() % 100 + 1;

			t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
			t = pow(t, (-1 * alpha));
			z = t * 100 + 1;
			if (y < z)
			{
			isGood = 1;
			points[w][3]++;
			points[x][3]++;
			//Connect Switch to Switch
			connection[x][w] = 1;
			connection[w][x] = 1;
			cout << endl << "Made connection " << v << endl;
			break;
			}
			cout << ".";
			}
			}
			}
			else if (traffic_help && traffic_optim)
			{
			if (traffic == 2)
			{
			w = rand() % (S - numHotspots);
			w = w + N;

			for(y = 0; y < numHotspots; y++)
			{
			if(w == con_hotspots[y])
			{
			w++;
			y = -1;
			}
			}

			if (points[w][3] < (kmax-1))
			{
			y = rand() % 100 + 1;

			t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
			t = pow(t, (-1 * alpha));
			z = t * 100 + 1;
			if (y < z)
			{
			isGood = 1;
			points[w][3]++;
			points[x][3]++;
			//Connect Switch to Switch
			connection[x][w] = 1;
			connection[w][x] = 1;
			cout << endl << "Made connection " << v << endl;
			break;
			}
			cout << ".";
			}
			}
			else if (traffic == 5)
			{
			for(y = 0; y < numTranspose; y++)
			{
			if (x == con_transpose[y][0])
			{
			z = y;
			t = 1;
			}
			else if(x == con_transpose[y][1])
			{
			z = y;
			t = 0;
			}
			}

			y = rand() % 100 + 1;

			if(y < (transPercent))
			{
			w = con_transpose[z][(int)t];
			}
			else
			{
			w = rand() % (S - numTranspose*2);
			w = w + N;

			for(y = 0; y < numTranspose; y++)
			{
			if(w == con_transpose[y][0] || w == con_transpose[y][1])
			{
			w++;
			y = -1;
			}
			}
			}

			if (points[w][3] < (kmax-1))
			{
			y = rand() % 100 + 1;

			t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
			t = pow(t, (-1 * alpha));
			z = t * 100 + 1;
			if (y < z)
			{
			isGood = 1;
			points[w][3]++;
			points[x][3]++;
			//Connect Switch to Switch
			connection[x][w] = 1;
			connection[w][x] = 1;
			cout << endl << "Made connection " << v << endl;
			break;
			}
			cout << ".";
			}
			}
			else
			{
			traffic_optim = 0;
			}
			}
			else
			{*/
			w = rand() % S;
			w = w + N;

			if (w != x)
			{
				if (points[w][3] < (kmax-1))
				{
					y = rand() % 100 + 1;

					t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
					t = pow(t, (-1 * alpha));
					z = t * 100 + 1;
					if (y < z)
					{
						isGood = 1;
						points[w][3]++;
						points[x][3]++;
						//Connect Switch to Switch
						connection[x][w] = 1;
						connection[w][x] = 1;
						cout << endl << "Made connection " << v << endl;
						break;
					}
					cout << ".";
				}
			}
			/*}

			if (num_tries >= 1000)
			{
			w = rand() % S;
			w = w + N;

			if (w != x)
			{
			if (points[w][3] < (kmax-1))
			{
			y = rand() % 100 + 1;

			t = sqrt((double) (points[x][0] - points[w][0]) * (points[x][0] - points[w][0]) + (points[x][1] - points[w][1]) * (points[x][1] - points[w][1]) + (points[x][2] - points[w][2]) * (points[x][2] - points[w][2]));
			t = pow(t, (-1 * alpha));
			z = t * 100 + 1;
			if (y < z)
			{
			isGood = 1;
			points[w][3]++;
			points[x][3]++;
			//Connect Switch to Switch
			connection[x][w] = 1;
			connection[w][x] = 1;
			cout << endl << "Made connection " << v << endl;
			break;
			}
			cout << ".";
			}
			}
			}*/
		}
	}

	for(v = 0; v < N+S; v++)
	{
		for(w = 0; w < N+S; w++)
		{
			if(connection[v][w] == -1)
			{
				lookupcycle[v][w] = -1;
			}
			if(connection[v][w] != -1)
			{
				t = sqrt((double) (points[v][0] - points[w][0]) * (points[v][0] - points[w][0]) + (points[v][1] - points[w][1]) * (points[v][1] - points[w][1]) + (points[v][2] - points[w][2]) * (points[v][2] - points[w][2]));
				t = ((double)((t * 20) / 9)) / 2;
				distmaxhelp = sqrt((double) (points[v][0] - points[w][0]) * (points[v][0] - points[w][0]) + (points[v][1] - points[w][1]) * (points[v][1] - points[w][1]) + (points[v][2] - points[w][2]) * (points[v][2] - points[w][2]));
				distmaxhelp = ((distmaxhelp * 20.0) / 9.0);
				if (distmaxhelp > maxmaxmax)
					maxmaxmax = distmaxhelp;

				lookupcycle[v][w] = t;
			}
		}
	}

	outFile << "Longest Wire is: " << maxmaxmax << endl;
	outFile << "********" << endl;
	for(v = 0; v < N+S; v++)
	{
		for(w = 0; w < N+S; w++)
			outFile << lookupcycle[v][w] << ",";
		outFile << endl;
	}

	outFile << endl << "**********" << endl << endl;

	//Fixing memory leak from points
	for(v = 0; v < N+S; v++)
	{
		free(points[v]);
	}
	free(points);
	return;
}

void addWireless()
{
	int rcount;
	int ccount;

	int iterations; 
	int wire;

	int r_c;
	int tracker;
	int flagger = 0;

	double orig_count;
	double o_count;
	double n_count;

	for(rcount = 0; rcount < numSwitches; rcount++)
		for(ccount = 0; ccount < numSwitches; ccount++)
			old_c[rcount][ccount] = orig_c[rcount][ccount];

	for(rcount = 0; rcount < numIps; rcount++)
		for(ccount = 0; ccount < numIps; ccount++)
			ohop[rcount][ccount] = orighop[rcount][ccount];

	for(rcount = 0; rcount < numIps; rcount++)
		for(ccount = rcount; ccount < numIps; ccount++)
			if(rcount != ccount)
				orig_count += orighop[rcount][ccount];

	orig_count /= (((numIps*numIps) / 2) - numIps);
	o_count = orig_count;


	for(iterations = 0; iterations < 1000; iterations++)
	{

		for(rcount = 0; rcount < numSwitches; rcount++)
			for(ccount = 0; ccount < numSwitches; ccount++)
				new_c[rcount][ccount] = orig_c[rcount][ccount];

		for(rcount = 0; rcount < numIps; rcount++)
			for(ccount = 0; ccount < numIps; ccount++)
				nhop[rcount][ccount] = orighop[rcount][ccount];

		for(wire = 0; wire < numWireless; wire++)
		{
			flagger = 0;

			while(!flagger)
			{
				hop = -1;
				r_c = rand() % numSwitches;
				for(rcount = 0; rcount < numSwitches; rcount++)
				{
					if ((new_c[r_c][rcount] != 10) && (!flagger))
					{
						if (hop < lookupcycle[r_c + numIps][rcount + numIps])
						{
							hop = lookupcycle[r_c + numIps][rcount + numIps];
							tracker = rcount;
							if (hop > 0)
							{
								flagger = 1;
							}
						}
					}
				}
			}

			new_c[tracker][r_c] = 10;
			new_c[r_c][tracker] = 10;
			nhop[tracker][r_c] -= hop + 1;
			nhop[r_c][tracker] -= hop + 1;

		}

		for(rcount = 0; rcount < numIps; rcount++)
			for(ccount = rcount; ccount < numIps; ccount++)
				if(rcount != ccount)
					n_count += nhop[rcount][ccount];

		n_count /= (((numIps*numIps) / 2) - numIps);

		if (n_count <= o_count) //new is better than old, so keep new
		{
			o_count = n_count;
			for(rcount = 0; rcount < numSwitches; rcount++)
				for(ccount = 0; ccount < numSwitches; ccount++)
					old_c[rcount][ccount] = new_c[rcount][ccount];

			for(rcount = 0; rcount < numIps; rcount++)
				for(ccount = 0; ccount < numIps; ccount++)
					ohop[rcount][ccount] = nhop[rcount][ccount];
		}
		else if ( o_count < n_count ) //old is better than new, so keep old if a probability says to
		{
			if (exp((o_count - n_count) / (1 / iterations)) > (rand() / RAND_MAX))
			{
				o_count = n_count;
				for(rcount = 0; rcount < numSwitches; rcount++)
					for(ccount = 0; ccount < numSwitches; ccount++)
						old_c[rcount][ccount] = new_c[rcount][ccount];

				for(rcount = 0; rcount < numIps; rcount++)
					for(ccount = 0; ccount < numIps; ccount++)
						ohop[rcount][ccount] = nhop[rcount][ccount];
			}
		}		
	}

	if (o_count <= orig_count) //(new) is more optimized so change it
	{
		for(rcount = 0; rcount < numSwitches; rcount++)
			for(ccount = 0; ccount < numSwitches; ccount++)
				orig_c[rcount][ccount] = old_c[rcount][ccount];

		for(rcount = 0; rcount < numIps; rcount++)
			for(ccount = 0; ccount < numIps; ccount++)
				orighop[rcount][ccount] = ohop[rcount][ccount];
	}
	else //original was the most optimized
	{
		cout << "\nOriginal was better!\n\n";
		failure = 0;
	}

	return;
}

void mst_prim(int tree_number)
{
	int V_sum = 0;
	int count0 = 0;
	int count1 = 0;
	int count2 = 0;
	int count3 = 0;

	for(int temp_count1 = 0; temp_count1 < MST_N; temp_count1++)
	{
		for(int temp_count2 = 0; temp_count2 < MST_N; temp_count2++)
		{
			UpTree[temp_count1][temp_count2][tree_number] = 0;
			DownTree[temp_count1][temp_count2][tree_number] = 0;
			SubTreeLabel[tree_number][temp_count1][temp_count2] = 0;
		}
		V[temp_count1][tree_number] = 0;
		L[temp_count1][tree_number] = 0;
		D[temp_count1][tree_number] = 0;
	}
	V[TreeRoot[tree_number]][tree_number] = 1;
	L[TreeRoot[tree_number]][tree_number] = 0;
	SubTreeLabel[tree_number][TreeRoot[tree_number]][0] = 0;

	ofstream sw_connection("connection_file.txt");
	for(count1 = 0; count1 < numNodes; count1++)
	{
		for(count2 = 0; count2 < numNodes; count2++)
		{
			sw_connection << connection[count1][count2] << " ";
		}
		sw_connection << endl;
	}
	sw_connection.close();

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = 0; count2 < MST_N; count2++)
		{
			if(connection[count1+MST_N][count2+MST_N] != -1)
				C[count1][count2] = 1;
			if(connection[count1+MST_N][count2+MST_N] == -1)
				C[count1][count2] = -1;
		}
	}

	for(count0 = 0; count0 < MST_N+1; count0++)
	{
		for(count1 = 0; count1 < MST_N; count1++)
		{
			if(V[count1][tree_number] == 1) //if vertex count1 is alread in V
			{
				for(count2 = 0; count2 < MST_N; count2++)
				{
					if(C[count1][count2] != -1) //selecting an edge from vertex count1 without sorting
					{
						if(D[count1][tree_number] <= 3)
						{
							if(V[count2][tree_number] == 0) //if vertex count2 is NOT in V
							{
								V[count2][tree_number] = 1; //add count2 to V
								DownTree[count1][count2][tree_number] = C[count1][count2]; //add count1-count2 to E
								L[count2][tree_number] = L[count1][tree_number] + 1; //one level below its parent node
								D[count1][tree_number] = D[count1][tree_number] + 1; //number of children of countq (parent)
								for(count3 = 0; count3 < MST_N; count3++)
								{
									SubTreeLabel[tree_number][count2][count3] = SubTreeLabel[tree_number][count1][count3]; //copy over previous subtree label
								}
								SubTreeLabel[tree_number][count2][L[count2][tree_number]] = D[count1][tree_number]; //adding current subtree/child number
							}
						}
					}
				}
			}
		}

		V_sum = 0;
		for(count1 = 0; count1 < MST_N; count1++)
		{
			V_sum += V[count1][tree_number];
		}

		if(V_sum == MST_N)
		{
			break;
		}
	}

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = count1; count2 < MST_N; count2++)
		{
			DownTree[count2][count1][tree_number] = DownTree[count1][count2][tree_number];
		}
		for(count2 = 0; count2 < MST_N; count2++)
		{
			UpTree[count1][count2][tree_number] = DownTree[count1][count2][tree_number];
		}
	}

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = 0; count2 < MST_N; count2++)
		{
			if((C[count1][count2]!= -1) && (DownTree[count1][count2][tree_number] == 0))
			{
				UpTree[count1][count2][tree_number] = C[count1][count2];
			}
		}
	}

	ofstream tree_label("sw_mst_label.txt");
	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = 0; count2 < MST_N; count2++)
		{
			tree_label << SubTreeLabel[tree_number][count1][count2] << " ";
		}
		tree_label << endl;
	}
	tree_label.close();

	return;
}

int ss_route_mst(int current_switch, int destination_switch, int tree_number)
{
	int next_switch = -1;

	int SuccessorCount = 0;
	int Successors[MST_N];

	// int MinDistance = 100000000000000; // bug: integer overflow
	long MinDistance = 100000000000000; // yuchen: bug fixed
	int Distance = -1;
	int MinNode = -1;

	int temp_count1 = 0;
	int temp_count2 = 0;
	int temp_count3 = 0;

	if(current_switch != destination_switch)
	{
		SuccessorCount = 0;
		for(temp_count1 = 0; temp_count1 < MST_N; temp_count1++)
		{
			Successors[temp_count1] = 0;
		}

		for(temp_count1 = 0; temp_count1 < MST_N; temp_count1++)
		{
			if(UpTree[current_switch][temp_count1][tree_number] == 1)
			{
				Successors[SuccessorCount] = temp_count1;
				SuccessorCount++;
			}
		}

		MinDistance = 100000000000000;
		MinNode = -1;

		if(SuccessorCount > 1)
		{
			for(temp_count1 = 0; temp_count1 < SuccessorCount; temp_count1++)
			{
				Distance = 0;
				for(temp_count2 = 0; temp_count2 < MST_N; temp_count2++)
				{
					if(SubTreeLabel[tree_number][destination_switch][temp_count2] != SubTreeLabel[tree_number][Successors[temp_count1]][temp_count2])
					{
						for(temp_count3 = temp_count2; temp_count3 < MST_N; temp_count3++)
						{
							if(SubTreeLabel[tree_number][destination_switch][temp_count3] != 0)
							{
								Distance++;
							}
							if(SubTreeLabel[tree_number][Successors[temp_count1]][temp_count3] != 0)
							{
								Distance++;
							}
						}
						break;
					}
				}

				if(Distance < MinDistance)
				{
					MinDistance = Distance;
					MinNode = Successors[temp_count1];
				}
			}
		}
		else
		{
			MinNode = Successors[0];
		}

		if(MinNode == -1)
		{
			cout << "Error in MST routing: ss_route_mst()" << endl << endl;
		}

		next_switch = MinNode;
	}
	else
	{
		next_switch = current_switch;
	}

	if(next_switch == -1)
	{
		cout << "Error in MST routing: ss_route_mst()" << endl << endl;
	}

	return next_switch;
}

void Dijkstra(int source)
{
	int alt = 0;
	int dist[MST_N];
	int previous[MST_N];
	int next[MST_N];
	int Q[MST_N];
	int sum_Q = 0;

	int v = 0;
	int u = -1;
	int minimum = 10000;
	int minimum_vertex = -1;

	for(v = 0; v < MST_N; v++)
	{
		dist[v] = 9999;
		previous[v] = -1;
		next[v] = -1;
		Q[v] = 0;
	}
	dist[source] = 0;

	while(sum_Q < MST_N)
	{
		minimum = 10000;
		minimum_vertex = -1;
		for(v = 0; v < MST_N; v++)
		{
			if(Q[v] == 0)
			{
				if(dist[v] < minimum)
				{
					minimum = dist[v];
					minimum_vertex = v;
				}
			}
		}

		Q[minimum_vertex] = 1;
		if (dist[minimum_vertex] == 9999)
		{
			cout << "Error in connection, not all nodes are accessible to each other!" << endl << endl;
			return;
		}

		for(v = 0; v < MST_N; v++)
		{
			if(Q[v] == 0)
			{
				if(connection[minimum_vertex+numIps][v+numIps] == 1)
				{
					alt = dist[minimum_vertex] + 1;
					if(alt < dist[v])
					{
						dist[v] = alt;
						previous[v] = minimum_vertex;

						if(next[minimum_vertex] ==  -1)
						{
							next[v] = v;
						}
						else
						{
							next[v] = next[minimum_vertex];
						}
					}
				}
			}
		}

		sum_Q = 0;
		for(v = 0; v < MST_N; v++)
		{
			sum_Q += Q[v];
		}
	}

	//fix the 'next' array to have switches be at the proper node indicies
	for(v = 0; v < MST_N; v++)
	{
		if(next[v] != -1)
		{
			next[v] += numIps;
		}
	}

	int real_source = source + numIps;
	for(v = 0; v < numNodes; v++)
	{
		if(v < numIps)
		{
			if(v == source)
			{
				lookup[real_source][v] = source;
			}
			else
			{
				lookup[real_source][v] = next[v];
			}
		}
		else
		{
			if(v == real_source)
			{
				lookup[real_source][v] = -1;
			}
			else
			{
				lookup[real_source][v] = next[(v-numIps)];
			}
		}
	}

	return;
}

void BFS(int tree_number)
{
	int V_sum = 0;
	int count0 = 0;
	int count1 = 0;
	int count2 = 0;
	int count3 = 0;
	int current_level = 0;

	for(int temp_count1 = 0; temp_count1 < MST_N; temp_count1++)
	{
		for(int temp_count2 = 0; temp_count2 < MST_N; temp_count2++)
		{
			UpTree[temp_count1][temp_count2][tree_number] = 0;
			DownTree[temp_count1][temp_count2][tree_number] = 0;
			SubTreeLabel[tree_number][temp_count1][temp_count2] = 0;
			connections[temp_count1][temp_count2][tree_number] = '.';
		}
		V[temp_count1][tree_number] = 0;
		L[temp_count1][tree_number] = 0;
		D[temp_count1][tree_number] = 0;
	}
	V[TreeRoot[tree_number]][tree_number] = 1;
	L[TreeRoot[tree_number]][tree_number] = 0;
	SubTreeLabel[tree_number][TreeRoot[tree_number]][0] = 0;

	//ofstream sw_connection("connection_file.txt");
	//for(count1 = 0; count1 < numNodes; count1++)
	//{
	//	for(count2 = 0; count2 < numNodes; count2++)
	//	{
	//		sw_connection << connection[count1][count2] << " ";
	//	}
	//	sw_connection << endl;
	//}
	//sw_connection.close();

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = 0; count2 < MST_N; count2++)
		{
			if(connection[count1+MST_N][count2+MST_N] != -1)
				C[count1][count2] = 1;
			if(connection[count1+MST_N][count2+MST_N] == -1)
				C[count1][count2] = -1;
		}
	}



	for(count0 = 0; count0 < MST_N+1; count0++)
	{
		for(count1 = 0; count1 < MST_N; count1++)
		{
			if(V[count1][tree_number] == 1)
			{
				if(L[count1][tree_number] == current_level)
				{
					for(count2 = 0; count2 < MST_N; count2++)
					{
						if(C[count1][count2] != -1)
						{
							//if(D[count1][tree_number] <= 1)
							//{
							if(V[count2][tree_number] == 0)
							{
								V[count2][tree_number] = 1;
								DownTree[count1][count2][tree_number] = C[count1][count2];
								connections[count1][count2][tree_number] = 'D';
								connections[count2][count1][tree_number] = 'U';
								L[count2][tree_number] = L[count1][tree_number] + 1;
								D[count1][tree_number] = D[count1][tree_number] + 1;
								for(count3 = 0; count3 < MST_N; count3++)
								{
									SubTreeLabel[tree_number][count2][count3] = SubTreeLabel[tree_number][count1][count3];
								}
								SubTreeLabel[tree_number][count2][L[count2][tree_number]] = D[count1][tree_number];
							}
							//}
						}
					}
				}
			}
		}
		current_level++;

		V_sum = 0;
		for(count1 = 0; count1 < MST_N; count1++)
		{
			V_sum += V[count1][tree_number];
		}

		if(V_sum == MST_N)
		{
			break;
		}
	}

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = count1; count2 < MST_N; count2++)
		{
			DownTree[count2][count1][tree_number] = DownTree[count1][count2][tree_number];
		}
		for(count2 = 0; count2 < MST_N; count2++)
		{
			UpTree[count1][count2][tree_number] = DownTree[count1][count2][tree_number];
		}
	}

	for(count1 = 0; count1 < MST_N; count1++)
	{
		for(count2 = 0; count2 < MST_N; count2++)
		{
			if((C[count1][count2] != -1) && (DownTree[count1][count2][tree_number] == 0))
			{
				UpTree[count1][count2][tree_number] = C[count1][count2];
				connections[count1][count2][tree_number] = 'S';
			}
		}
	}

	//ofstream tree_label("sw_mst_label.txt");
	//for(count1 = 0; count1 < MST_N; count1++)
	//{
	//	for(count2 = 0; count2 < MST_N; count2++)
	//	{
	//		tree_label << SubTreeLabel[tree_number][count1][count2] << " ";
	//	}
	//	tree_label << endl;
	//}
	//tree_label.close();

	return;
}

void buildRoutingTables(void) //called only once
{
	if(fMROOTS)
	{
		for(int tree_num = 0; tree_num < MTREES; tree_num++)
		{
			for(int i = 0; i < NUM_CORES; i++)
			{
				RT[i].address[tree_num] = SubTreeLabel[tree_num][i];

				if(tree_num == 0) //only do once
				{
					RT[i].ThrottleAttempts = 0;
					RT[i].commDensity = 0.0;
					RT[i].Throttled = false;

					for(int j = 0; j < NUM_CORES; j++)
					{
						if(connections[i][j][tree_num] != '.')
						{
							RT[i].numLinks++;
						}
					}
				}

				RT[i].Entries[tree_num] = new RoutingTableEntry[RT[i].numLinks];

				int k = 0;
				for(int j = 0; j < NUM_CORES; j++)
				{
					if (connections[i][j][tree_num] != '.') // There is a connection between the two, create it.
					{
						switch (connections[i][j][tree_num])
						{
						case 'D':
							RT[i].Entries[tree_num][k].LinkType = Down;
							RT[i].Entries[tree_num][k].ChannelType = Wireline;
							break;
						case 'U':
							RT[i].Entries[tree_num][k].LinkType = Up;
							RT[i].Entries[tree_num][k].ChannelType = Wireline;
							break;
						case '1':
							RT[i].Entries[tree_num][k].LinkType = WirelessShortcut;
							RT[i].Entries[tree_num][k].ChannelType = Wireless1;
							break;
						case '2':
							RT[i].Entries[tree_num][k].LinkType = WirelessShortcut;
							RT[i].Entries[tree_num][k].ChannelType = Wireless2;
							break;
						case '3':
							RT[i].Entries[tree_num][k].LinkType = WirelessShortcut;
							RT[i].Entries[tree_num][k].ChannelType = Wireless3;
							break;
						case 'S':
							RT[i].Entries[tree_num][k].LinkType = WirelineShortcut;
							RT[i].Entries[tree_num][k].ChannelType = Wireline;
							break;
						default:
							RT[i].Entries[tree_num][k].LinkType = None; // If there is a connection, this case shouldn't happen...
							RT[i].Entries[tree_num][k].ChannelType = Wireline;
							break;
						}
						RT[i].Entries[tree_num][k].NextRouter = j;
						RT[i].Entries[tree_num][k].HasWirelessToken = false;

						k++;
					}
				}
			}

			if(GLOBAL)
			{
				for (int i = 0; i < NUM_CORES; i++)
				{
					for (int p = 0; p < NUM_PATHS; p++)
					{
						for (int j = 0; j < NUM_CORES; j++)
						{	
							mPath[i][j][tree_num][p].rank = NUM_PATHS + 1;
							for(int w = 0; w < 24; w++)
							{
								mPath[i][j][tree_num][p].path[w] = -1;
							}
						}
					}
				}
			}

			for (int i = 0; i < NUM_CORES; i++)
			{
				for (int k = 0; k < RT[i].numLinks; k++)
				{
					for (int j = 0; j < NUM_CORES; j++)
					{	// Distance between NEXT router and final destination
						RT[i].Entries[tree_num][k].DistanceFromFinalDestination[j] = tupleDifference(RT[RT[i].Entries[tree_num][k].NextRouter].address[tree_num], RT[j].address[tree_num]);
						RT[i].Entries[tree_num][k].ThrottlingRatio[j] = 1;
						RT[i].Entries[tree_num][k].Rank[j] = RT[i].numLinks + 1;
					}
				}
			}

			for (int i = 0; i < NUM_CORES; i++)
			{
				for (int j = 0; j < NUM_CORES; j++)
				{
					int rank = 0;
					for (int k = 0; k < RT[i].numLinks; k++)
					{
						LinkTypes minType = None;
						int kmin = 0;
						int min = 999;
						for (int k1 = 0; k1 < RT[i].numLinks; k1++)
						{
							if (RT[i].Entries[tree_num][k1].Rank[j] == RT[i].numLinks + 1 && (min > RT[i].Entries[tree_num][k1].DistanceFromFinalDestination[j] 
							|| (min == RT[i].Entries[tree_num][k1].DistanceFromFinalDestination[j] && minType != WirelineShortcut && RT[i].Entries[tree_num][k1].LinkType == WirelineShortcut)
								|| (min == RT[i].Entries[tree_num][k1].DistanceFromFinalDestination[j] && (minType != WirelessShortcut && minType != WirelineShortcut) && RT[i].Entries[tree_num][k1].LinkType == WirelessShortcut)))
							{
								min = RT[i].Entries[tree_num][k1].DistanceFromFinalDestination[j];
								kmin = k1;
								minType = RT[i].Entries[tree_num][k1].LinkType;
							}
						}

						RT[i].Entries[tree_num][kmin].Rank[j] = rank++;
					}
				}
			}
		}
	}
	if(fALASH)
	{
		for(int i = 0; i < NUM_CORES; i++)
		{

			RT[i].ThrottleAttempts = 0;
			RT[i].commDensity = 0.0;
			RT[i].Throttled = false;

			for(int j = 0; j < NUM_CORES; j++)
			{
				if(connections[i][j][0] != '.')
				{
					RT[i].numLinks++;
				}
			}


			RT[i].Entries[0] = new RoutingTableEntry[RT[i].numLinks];

			int k = 0;
			for(int j = 0; j < NUM_CORES; j++)
			{
				if (connections[i][j][0] != '.') // There is a connection between the two, create it.
				{
					switch (connections[i][j][0])
					{
					case 'D':
						RT[i].Entries[0][k].LinkType = Down;
						RT[i].Entries[0][k].ChannelType = Wireline;
						break;
					case '1':
						RT[i].Entries[0][k].LinkType = WirelessShortcut;
						RT[i].Entries[0][k].ChannelType = Wireless1;
						break;
					case '2':
						RT[i].Entries[0][k].LinkType = WirelessShortcut;
						RT[i].Entries[0][k].ChannelType = Wireless2;
						break;
					case '3':
						RT[i].Entries[0][k].LinkType = WirelessShortcut;
						RT[i].Entries[0][k].ChannelType = Wireless3;
						break;
					default:
						RT[i].Entries[0][k].LinkType = None; // If there is a connection, this case shouldn't happen...
						RT[i].Entries[0][k].ChannelType = Wireline;
						break;
					}
					RT[i].Entries[0][k].NextRouter = j;
					RT[i].Entries[0][k].HasWirelessToken = false;

					k++;
				}
			}
		}

		if(GLOBAL)
		{
			for (int i = 0; i < NUM_CORES; i++)
			{
				for (int p = 0; p < NUM_PATHS; p++)
				{
					for (int j = 0; j < NUM_CORES; j++)
					{	
						mPath[i][j][0][p].rank = NUM_PATHS + 1;
						for(int w = 0; w < 24; w++)
						{
							mPath[i][j][0][p].path[w] = -1;
						}
					}
				}
			}
		}

		for (int i = 0; i < NUM_CORES; i++)
		{
			for (int k = 0; k < RT[i].numLinks; k++)
			{
				for (int j = 0; j < NUM_CORES; j++)
				{	// Distance between NEXT router and final destination
					RT[i].Entries[0][k].DistanceFromFinalDestination[j] = tupleDifference(RT[RT[i].Entries[0][k].NextRouter].address[0], RT[j].address[0]);
					RT[i].Entries[0][k].ThrottlingRatio[j] = 1;
					RT[i].Entries[0][k].Rank[j] = RT[i].numLinks + 1;
				}
			}
		}

		for (int i = 0; i < NUM_CORES; i++)
		{
			for (int j = 0; j < NUM_CORES; j++)
			{
				int rank = 0;
				for (int k = 0; k < RT[i].numLinks; k++)
				{
					LinkTypes minType = None;
					int kmin = 0;
					int min = 999;
					for (int k1 = 0; k1 < RT[i].numLinks; k1++)
					{
						if (RT[i].Entries[0][k1].Rank[j] == RT[i].numLinks + 1 && (min > RT[i].Entries[0][k1].DistanceFromFinalDestination[j] 
						|| (min == RT[i].Entries[0][k1].DistanceFromFinalDestination[j] && minType != WirelineShortcut && RT[i].Entries[0][k1].LinkType == WirelineShortcut)
							|| (min == RT[i].Entries[0][k1].DistanceFromFinalDestination[j] && (minType != WirelessShortcut && minType != WirelineShortcut) && RT[i].Entries[0][k1].LinkType == WirelessShortcut)))
						{
							min = RT[i].Entries[0][k1].DistanceFromFinalDestination[j];
							kmin = k1;
							minType = RT[i].Entries[0][k1].LinkType;
						}
					}

					RT[i].Entries[0][kmin].Rank[j] = rank++;
				}
			}
		}
	}
	return;
}

void freeRoutingTables(void) //called only once at end
{
	for(int i = 0; i < NUM_CORES; i++)
	{
		for(int j = 0; j < MTREES; j++)
		{
			free(RT[i].Entries[j]);
		}
	}
}

void updateRoutingTables(int router) //called after every WINDOW_SIZE cycles
{
	for(int tree_number = 0; tree_number < MTREES; tree_number++)
	{
		for(int i = 0; i < NUM_CORES; i++)
		{
			for(int j = 0; j < NUM_CORES; j++)
			{
				for(int k = 0; k < RT[i].numLinks; k++)
				{
					//if(GLOBAL)
					//{
					//RT[i].Entries[tree_number][k].ThrottlingRatio[j] = (1.0/(RT[router].ThrottleAttempts + 1));
					//}
					//else
					//{
					if(RT[i].Entries[tree_number][k].NextRouter == router && router == j) // If our final destination is the problem router, we still must get there... So take this link!
					{
						RT[i].Entries[tree_number][k].ThrottlingRatio[j] = 1;
					}
					else if(RT[i].Entries[tree_number][k].NextRouter == router && RT[i].Entries[tree_number][k].DistanceFromFinalDestination[j] <= 1)
					{
						RT[i].Entries[tree_number][k].ThrottlingRatio[j] = 1;
					}
					else if(RT[i].Entries[tree_number][k].NextRouter == router && router == TreeRoot[tree_number]) //don't throttle a tree root
					{
						RT[i].Entries[tree_number][k].ThrottlingRatio[j] = 1;
					}
					else if (RT[i].Entries[tree_number][k].NextRouter == router && RT[i].Entries[tree_number][k].LinkType != Down) // Should not throttle downlinks, if it is our only way to final dest.
					{					
						RT[i].Entries[tree_number][k].ThrottlingRatio[j] = pow(1.0/(RT[i].Entries[tree_number][k].DistanceFromFinalDestination[j]*RT[i].Entries[tree_number][k].LinkType),RT[router].ThrottleAttempts);
					}
					//}
				}
			}
		}
	}
}

void updateWirelessLinks(int t1, int t2, int t3) //called every cycle for wireless channels
{
	for(int tree_number = 0; tree_number < MTREES; tree_number++)
	{
		for(int i = 0; i < NUM_CORES; i++)
		{
			for(int k = 0; k < RT[i].numLinks; k++)
			{
				if(i == t1 && RT[i].Entries[tree_number][k].ChannelType == Wireless1 && !stallToken[0])//[tree_number])
				{
					RT[i].Entries[tree_number][k].HasWirelessToken = true;
				}
				else if(i == t2 && RT[i].Entries[tree_number][k].ChannelType == Wireless2 && !stallToken[1])//[tree_number])
				{
					RT[i].Entries[tree_number][k].HasWirelessToken = true;
				}
				else if(i == t3 && RT[i].Entries[tree_number][k].ChannelType == Wireless3 && !stallToken[2])//[tree_number])
				{
					RT[i].Entries[tree_number][k].HasWirelessToken = true;
				}
				else
				{
					RT[i].Entries[tree_number][k].HasWirelessToken = false;
				}
			}
		}
	}
}

int thermalRerout(int currentRouter, int destinationRouter, int previousRouter, int tree_number) //code called to give next router
{
	//double randomNum = ((double) rand() / (double) RAND_MAX);
	//double randomNum = 0.0;

	double randomNum = 0.0;
	random_number_file >> randomNum;
	random_number_count++;
	if(random_number_count >= 10000)
	{
		random_number_count = 0;
		random_number_file.close();
		random_number_file.open("random.txt");
	}

	double ksum = 0.0;
	bool done = false;

	for(int rank = 0; rank < RT[currentRouter].numLinks; rank++)
	{
		for (int k = 0; k < RT[currentRouter].numLinks; k++)
		{
			if(RT[currentRouter].Entries[tree_number][k].Rank[destinationRouter] == rank)
			{
				if (RT[currentRouter].Entries[tree_number][k].LinkType == Down)
				{
					done = true;
					break;
				}
				if(!badPath(currentRouter, destinationRouter, RT[currentRouter].Entries[tree_number][k].NextRouter, tree_number))
				{
					ksum += RT[currentRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter];
				}
				if (RT[currentRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter] == 1.0)
				{
					done = true;
					break;
				}
				break;
			}
		}
		if (done)
			break;
	}

	if (ksum == 0.0) // if our 1st ranked path was downtree, force ksum to 1.
		ksum = 1.0;

	double sumSoFar = 0.0;

	int lastAvailableLink = 999;
	for(int rank = 0; rank < RT[currentRouter].numLinks; rank++)
	{
		for(int k = 0; k < RT[currentRouter].numLinks; k++)
		{
			if(RT[currentRouter].Entries[tree_number][k].Rank[destinationRouter] == rank)
			{
				if (randomNum <= (RT[currentRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter])/ksum + sumSoFar)
				{
					if (!(RT[currentRouter].Entries[tree_number][k].LinkType == WirelessShortcut && RT[currentRouter].Entries[tree_number][k].HasWirelessToken == false))
					{
						if(RT[currentRouter].Entries[tree_number][k].LinkType == WirelessShortcut && RT[currentRouter].Entries[tree_number][k].HasWirelessToken == true)
						{
							tokenPacketCount[(RT[currentRouter].Entries[tree_number][k].ChannelType-1)]++;
							if(tokenPacketCount[(RT[currentRouter].Entries[tree_number][k].ChannelType-1)] >= MAX_TOKEN_PACKETS)
							{
								stallToken[(RT[currentRouter].Entries[tree_number][k].ChannelType-1)] = true; //[tree_number] = true;
							}
						}

						if(!badPath(currentRouter, destinationRouter, RT[currentRouter].Entries[tree_number][k].NextRouter, tree_number))
						{
							return RT[currentRouter].Entries[tree_number][k].NextRouter;
						}
					}	
				}
				if (!(RT[currentRouter].Entries[tree_number][k].LinkType == WirelessShortcut && RT[currentRouter].Entries[tree_number][k].HasWirelessToken == false))
				{
					lastAvailableLink = k;
				}
				sumSoFar += RT[currentRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter]/ksum;
				break;
			}
		}
	}

	return RT[currentRouter].Entries[tree_number][lastAvailableLink].NextRouter; // IF THIS RETURNS 999, IS AN ERROR!
	//for(int k = 0; k < RT[currentRouter].numLinks; k++)
	//{
	//	if(RT[currentRouter].Entries[tree_number][k].Rank[destinationRouter] == 0)
	//		return RT[currentRouter].Entries[tree_number][k].NextRouter;
	//}
}

int tupleDifference(int *address1, int *address2) //called from update routing and build routing
{
	int prefix = 1;
	int distance = 0;

	for (int t = 0; t < ADDRESS_LENGTH; t++)
	{
		if (prefix == 1)
			if (address1[t] != address2[t])
				prefix = 0;

		if (prefix == 0)
		{
			if (address1[t] != 0)
				distance++;
			if (address2[t] != 0)
				distance++;
		}
	}

	return distance;
}

double maxLength(void)
{
	//int bestTrees[4] = {0};
	int maxHops = 0;

	for (int i = 0; i < NUM_CORES; i++)
	{
		for (int j = 0; j < NUM_CORES; j++)
		{
			for (int k = 0; k < NUM_CORES; k++)
			{
				for (int l = 0; l < NUM_CORES; l++)
				{
					if (i == j || i == k || i == l || j == k || j == l || k == l)
					{
						//do nothing
					}
					else
					{
						TreeRoot[0] = i; 
						TreeRoot[1] = j;
						TreeRoot[2] = k;
						TreeRoot[3] = l;
						for (int trees = 0; trees < MTREES; trees++)
						{
							BFS(trees);
						}

						int hopCount = 0;
						int c = i;
						while (c != j)
						{
							c = ss_route_mst(c,j, 0);
							hopCount++;
						}

						c = i;
						while (c != k)
						{
							c = ss_route_mst(c,k, 0);
							hopCount++;
						}

						c = i;
						while (c != l)
						{
							c = ss_route_mst(c,l, 0);
							hopCount++;
						}

						c = j;
						while (c != k)
						{
							c = ss_route_mst(c,k, 1);
							hopCount++;
						}

						c = j;
						while (c != l)
						{
							c = ss_route_mst(c,l, 1);
							hopCount++;
						}

						c = k;
						while (c != l)
						{
							c = ss_route_mst(c,l, 2);
							hopCount++;
						}

						if (maxHops <= hopCount)
						{
							maxHops = hopCount;
							//bestTrees = {i,j,k,l};
							printf("Max dist trees (%d,%d,%d,%d) = %lf!\n", i,j,k,l,maxHops/6.0);
						}

					}
				}
			}
		}
	}	

	return maxHops/6.0;
}

void addWirelessToSW(void)
{
	//channel 1 switches: 0, 4, 14, 36, 47
	//channel 2 switches: 3, 23, 25, 36
	//channel 3 switches: 8, 36, 49, 59, 63
	//gateway switches: 36
	//channel 1 nodes: 64, 68, 78, 100, 111
	//channel 2 nodes: 67, 87, 89, 100
	//channel 3 nodes: 72, 100, 113, 123, 127
	//gateway nodes: 100

	if(numPorts < 17)
	{
		cout << "Error in the number of ports! Simulation won't run properly!" << endl << endl;
		cout << "Wireless will NOT be added!" << endl << endl;
		return;
	}


	ofstream help_me("connection.txt");
	for(int i = 0; i < numNodes; i++)
	{
		for(int j = 0; j < numNodes; j++)
		{
			help_me << connection[i][j] << " ";
		}
		help_me << endl;
	}
	help_me.close();


	for(int count0 = 0; count0 < 5; count0++)
	{
		for(int count1 = 0; count1 < 5; count1++)
		{
			if(count0 != count1)
			{
				if((count0 < 4) && (count1 < 4))
				{
					C[channel_2_switch[count0]][channel_2_switch[count1]] = 1;

					connection[channel_2_node[count0]][channel_2_node[count1]] = nextPortNumbers[channel_2_switch[count1]];
					nextPortNumbers[channel_2_switch[count1]]++;
				}
				C[channel_1_switch[count0]][channel_1_switch[count1]] = 1;
				C[channel_3_switch[count0]][channel_3_switch[count1]] = 1;

				connection[channel_1_node[count0]][channel_1_node[count1]] = nextPortNumbers[channel_1_switch[count1]];
				nextPortNumbers[channel_1_switch[count1]]++;
				connection[channel_3_node[count0]][channel_3_node[count1]] = nextPortNumbers[channel_3_switch[count1]];
				nextPortNumbers[channel_3_switch[count1]]++;

				for(int tnum = 0; tnum < MTREES; tnum++)
				{
					if((count0 < 4) && (count1 < 4))
					{
						UpTree[channel_2_switch[count0]][channel_2_switch[count1]][tnum] = 1;
						connections[channel_2_switch[count0]][channel_2_switch[count1]][tnum] = '2';
					}
					UpTree[channel_1_switch[count0]][channel_1_switch[count1]][tnum] = 1;
					UpTree[channel_3_switch[count0]][channel_3_switch[count1]][tnum] = 1;
					connections[channel_1_switch[count0]][channel_1_switch[count1]][tnum] = '1';
					connections[channel_3_switch[count0]][channel_3_switch[count1]][tnum] = '3';

				}
			}
		}
	}

	ofstream help_me1("connection1.txt");
	for(int i = 0; i < numNodes; i++)
	{
		for(int j = 0; j < numNodes; j++)
		{
			help_me1 << connection[i][j] << " ";
		}
		help_me1 << endl;
	}
	help_me1.close();

	return;
}

void checkTokens(void)
{
	//tokenPortStart[]
	bool t1 = false;
	bool t2 = false;
	bool t3 = false;

	if(fMROOTS)
	{
		for(int p = 0; p < numPorts; p++)
		{
			for(int r = 0; r < numVirts*bufferDepth; r++)
			{
				if(token1*numPorts+p >= tokenPortStart[token1])
				{
					if(ports[token1*numPorts+p].o_buff[r] != 0 && t1)
					{
						t1 = false;
					}
				}

				if(token2*numPorts+p >= tokenPortStart[token2])
				{
					if(ports[token2*numPorts+p].o_buff[r] != 0 && t2)
					{
						t2 = false;
					}
				}

				if(token3*numPorts+p >= tokenPortStart[token3])
				{
					if(ports[token3*numPorts+p].o_buff[r] != 0 && t3)
					{
						t3 = false;
					}
				}
			}
		}
		if(t1)
		{
			for(int temp1 = 0; temp1 < 5; temp1++)
			{
				if(channel_1_switch[temp1] == token1)
				{
					token1 = channel_1_switch[((temp1+1)%5)];
					stallToken[0]=false;//[treeToken] = false;
					tokenPacketCount[0] = 0;
					break;
				}
			}
		}
		if(t2)
		{
			for(int temp1 = 0; temp1 < 4; temp1++)
			{
				if(channel_2_switch[temp1] == token2)
				{
					token2 = channel_2_switch[((temp1+1)%4)];
					stallToken[1]=false;//[treeToken] = false;
					tokenPacketCount[1] = 0;
					break;
				}
			}
		}
		if(t3)
		{
			for(int temp1 = 0; temp1 < 5; temp1++)
			{
				if(channel_3_switch[temp1] == token3)
				{
					token3 = channel_3_switch[((temp1+1)%5)];
					stallToken[2]=false;//[treeToken] = false;
					tokenPacketCount[2] = 0;
					break;
				}
			}
		}
	}
	else if(fLASH || fALASH)
	{
		int portnum = 0;
		for(int p = 0; p < 5; p++)
		{
			if(channel_1_node[p] != token1)
			{
				for(int r = 0; r < numVirts*bufferDepth;r++)
				{
					portnum = connection[channel_1_node[p]][token1];
					if(ports[portnum].o_buff[r] != 0 && t1)
						t1 = false;
				}
			}
		}
		for(int p = 0; p < 4; p++)
		{
			if(channel_2_node[p] != token2)
			{
				for(int r = 0; r < numVirts*bufferDepth;r++)
				{
					portnum = connection[channel_2_node[p]][token2];
					if(ports[portnum].o_buff[r] != 0 && t2)
						t2 = false;
				}
			}
		}
		for(int p = 0; p < 5; p++)
		{
			if(channel_3_node[p] != token3)
			{
				for(int r = 0; r < numVirts*bufferDepth;r++)
				{
					portnum = connection[channel_3_node[p]][token3];
					if(ports[portnum].o_buff[r] != 0 && t3)
						t3 = false;
				}
			}
		}
		if(t1)
		{
			for(int temp1 = 0; temp1 < 5; temp1++)
			{
				if(channel_1_node[temp1] == token1)
				{
					if(TOKEN_MAC)
					{
						token1 = channel_1_node[((temp1+1)%5)];
					}
					stallToken[0]=false;//[treeToken] = false;
					free_token[0]=true;
					tokenPacketCount[0] = 0;
					break;
				}
			}
		}
		if(t2)
		{
			for(int temp1 = 0; temp1 < 4; temp1++)
			{
				if(channel_2_node[temp1] == token2)
				{
					if(TOKEN_MAC)
					{
						token2 = channel_2_node[((temp1+1)%4)];
					}
					stallToken[1]=false;//[treeToken] = false;
					free_token[1]=true;
					tokenPacketCount[1] = 0;
					break;
				}
			}
		}
		if(t3)
		{
			for(int temp1 = 0; temp1 < 5; temp1++)
			{
				if(channel_3_node[temp1] == token3)
				{
					if(TOKEN_MAC)
					{
						token3 = channel_3_node[((temp1+1)%5)];
					}
					stallToken[2]=false;//[treeToken] = false;
					free_token[2]=true;
					tokenPacketCount[2] = 0;
					break;
				}
			}
		}
	}


}



void initWirelessTokens(void)
{
	//for(int t = 0; t < 3; t++)
	//{
	//	for(int tt = 0; tt < MTREES; tt++)
	//	{
	//		stallToken[t][tt] = true;
	//	}
	//}
	//int r1 = 0;
	//int r2 = 1;
	//int r3 = 2;

	stallToken[0] = false;//[r1] = false;
	stallToken[1] = false;//[r2] = false;
	stallToken[2] = false;//[r3] = false;
}

void makeFij(void)
{
	ifstream fij("sw_fijbenchmark.txt");

	if(!fij.good())
	{
		cout << "Error in reading benchmark file!" << endl << endl;
	}
	else
	{
		for(int row = 0; row < MST_N; row++)
		{
			double tempSUM = 0.0;
			double temp_num = 0.0;
			for(int col = 0; col < MST_N; col++)
			{
				fij >> temp_num;

				FijMATRIX[row][col] = temp_num;
				tempSUM += temp_num;
			}
			benchmarkLoad[row] = tempSUM;
		}
	}
}

bool badPath(int currentRouter, int destinationRouter, int nextRouter, int tree_number)
{
	//returns true if BAD path
	int currentDistance = tupleDifference(RT[currentRouter].address[tree_number], RT[destinationRouter].address[tree_number]);
	int numThrottled = 0;

	if(nextRouter != destinationRouter)
	{
		for(int k = 0; k < RT[nextRouter].numLinks; k++)
		{
			if(RT[nextRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter] < 1.0)
			{
				numThrottled++;
			}
			if(RT[nextRouter].Entries[tree_number][k].NextRouter == currentRouter && RT[nextRouter].numLinks == 1)
			{
				return true;
			}
			if(RT[nextRouter].Entries[tree_number][k].DistanceFromFinalDestination[destinationRouter] < currentDistance && RT[nextRouter].Entries[tree_number][k].ThrottlingRatio[destinationRouter] == 1.0)
			{
				return false;
			}
		}

		if(numThrottled == RT[nextRouter].numLinks-1)
		{
			return true;
		}
	}

	return false;
}

int pathLength1(int source, int dest, int tree_number)
{
	int avgHopCount = 0;
	int numPaths = 0;
	int maxHops = 0;
	int maxHopDest = 0;
	int maxHopSour = 0;
	FILE *outfile = NULL;


	if (source != dest) //No paths here
	{
		int hopCount = 0;
		int c = source;

		while (1)
		{
			c = ss_route_mst(c,dest, tree_number);
			hopCount++;
			if (c == dest)
				break;
		}

		avgHopCount += hopCount;
	}

	return avgHopCount;
}

void findPaths(int hop_count, int source, int current, int dest, int tree, LinkTypes prevLink)
{
	if(wirelessP >= NUM_WI_PATHS && prevLink == WirelessShortcut)
	{
		path_length = -1;
		return;//too many wireless paths, need only wireline
	}
	else if(wirelessP < NUM_WI_PATHS && prevLink == WirelessShortcut)
	{
		wirelessP++;
	}

	if(current != dest)
	{
		if(path_length > pathLength1(source, dest, tree))
		{
			path_length = -1;
			return; //path too long
		}
		for(int temp = 0; temp < path_length; temp++)
		{
			if(current == ppath[temp])
			{
				path_length = -1;
				return; //path came back to itself
			}
		}

		for(int next = 0; next < RT[current].numLinks; next++)
		{
			ppath[hop_count] = current;
			path_length = hop_count+1;
			if (mPath[source][dest][tree][NUM_PATHS-1].plength == 0)
			{
				if(!(RT[current].Entries[tree][next].LinkType != Down && prevLink == Down) || prevLink != Down)
				{
					if(!(wirelessP >= NUM_WI_PATHS && prevLink == WirelessShortcut))
					{
						findPaths(hop_count+1, source, RT[current].Entries[tree][next].NextRouter, dest, tree, RT[current].Entries[tree][next].LinkType);
					}
				}
			}
		}
	}
	else
	{
		ppath[hop_count] = current;

		//if(length < mPath[source][dest][p].plength)
		//{
		//shift and insert new path and path length
		//}
		if (mPath[source][dest][tree][ppp].plength == 0)
		{
			mPath[source][dest][tree][ppp].plength = hop_count;
			for (int i = 0; i < 24; i++)
			{
				mPath[source][dest][tree][ppp].path[i] = ppath[i];
			}
		}
		ppp++;
	}
}

void rankPaths(int tree_number)
{
	for (int i = 0; i < NUM_CORES; i++)
	{
		for (int j = 0; j < NUM_CORES; j++)
		{
			if(i == 51 && j == 10 && (tree_number == 2 || tree_number == 3))
				i = i;
			int rank = 0;
			for (int p = 0; p < NUM_PATHS; p++)
			{
				int numWireless = 0;
				int minWireless = 999;
				int pmin = 0;
				int min = NUM_PATHS + 2;
				for (int p1 = 0; p1 < NUM_PATHS; p1++)
				{
					numWireless = 0;
					for(int w = 0; w < mPath[i][j][tree_number][p1].plength; w++)
					{
						for(int k = 0; k < RT[mPath[i][j][tree_number][p1].path[w]].numLinks; k++)
						{
							if (RT[mPath[i][j][tree_number][p1].path[w]].Entries[tree_number][k].NextRouter == mPath[i][j][tree_number][p1].path[w+1] && RT[mPath[i][j][tree_number][p1].path[w]].Entries[tree_number][k].LinkType == WirelessShortcut)
							{
								numWireless++;
							}
						}
					}

					if (mPath[i][j][tree_number][p1].rank == NUM_PATHS + 1 && (min > mPath[i][j][tree_number][p1].plength || (min == mPath[i][j][tree_number][p1].plength && minWireless > numWireless)) && mPath[i][j][tree_number][p1].path[0] != -1)
					{
						min = mPath[i][j][tree_number][p1].plength;
						pmin = p1;
						minWireless = numWireless;
					}
				}

				if(mPath[i][j][tree_number][pmin].path[0] != -1 && mPath[i][j][tree_number][pmin].rank == NUM_PATHS+1)
				{
					mPath[i][j][tree_number][pmin].rank = rank++;
				}
			}
		}
	}

}

int globalThermalRerout(int currentRouter, int sourceRouter, int destinationRouter, int *pathNumber, int tree_number)
{
	double randomNum = 0.0;
	random_number_file >> randomNum;
	random_number_count++;
	if(random_number_count >= 10000)
	{
		random_number_count = 0;
		random_number_file.close();
		random_number_file.open("random.txt");
	}

	bool done = false;
	double psum = 0.0;
	double path_ratio[NUM_PATHS] = {0.0};
	int pnum[NUM_PATHS];

	if(*pathNumber == -2) //Got to a WI and no token, so reroute using wireline only!
	{
		for(int rank = 0; rank < NUM_PATHS; rank++)
		{
			pnum[rank] = -1;
			path_ratio[rank] = 1.0;
			for(int p = 0; p < NUM_PATHS; p++)
			{
				if(mPath[sourceRouter][destinationRouter][tree_number][p].rank == rank)
				{
					pnum[rank] = p;
					for(int w = 0; w < 24; w++)
					{
						for(int k = 0; k < RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].numLinks; k++)
						{
							if(RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].Entries[tree_number][k].NextRouter == mPath[sourceRouter][destinationRouter][tree_number][p].path[w+1]
							&& ((RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].Entries[tree_number][k].LinkType == WirelessShortcut)))
							{
								path_ratio[rank] = 0.0;
								w = 25;
							}
						}

						if(mPath[sourceRouter][destinationRouter][tree_number][p].path[w] != destinationRouter)
						{
							path_ratio[rank] *= pow((1.0/(RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].ThrottleAttempts + 1.0)), RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].ThrottleAttempts);
						}
						if(mPath[sourceRouter][destinationRouter][tree_number][p].path[w] == destinationRouter)
						{
							w = 25;
						}
					}

					if(path_ratio[rank] == 1.0)
					{
						done = true;
					}
					else
					{
						path_ratio[rank] *= (1.0/mPath[sourceRouter][destinationRouter][tree_number][p].plength);
					}
					psum += path_ratio[rank];
				}

				if(done)
				{
					break;
				}
			}

			if(done)
			{
				break;
			}
		}

		double sumSoFar = 0.0;


		for(int p = 0; (pnum[p] != -1 && p < NUM_PATHS); p++)
		{
			if (randomNum <= (path_ratio[p])/psum + sumSoFar)
			{
				*pathNumber = pnum[p];
				//return (mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[1]); //let the finishing loop handle the return statement
				break;
			}

			sumSoFar += (path_ratio[p])/psum;
		}
	}


	if(*pathNumber == -1)
	{
		for(int rank = 0; rank < NUM_PATHS; rank++)
		{
			pnum[rank] = -1;
			path_ratio[rank] = 1.0;
			for(int p = 0; p < NUM_PATHS; p++)
			{
				if(mPath[sourceRouter][destinationRouter][tree_number][p].rank == rank)
				{
					pnum[rank] = p;
					for(int w = 0; w < 24; w++)
					{
						if(mPath[sourceRouter][destinationRouter][tree_number][p].path[w] != destinationRouter)
						{
							path_ratio[rank] *= (1.0/(RT[mPath[sourceRouter][destinationRouter][tree_number][p].path[w]].ThrottleAttempts + 1.0));
						}
						if(mPath[sourceRouter][destinationRouter][tree_number][p].path[w] == destinationRouter)
						{
							w = 25;
						}
					}

					if(path_ratio[rank] == 1.0)
					{
						done = true;
					}
					else
					{
						path_ratio[rank] *= (1.0/mPath[sourceRouter][destinationRouter][tree_number][p].plength);
					}
					psum += path_ratio[rank];
				}

				if(done)
				{
					break;
				}
			}

			if(done)
			{
				break;
			}
		}

		double sumSoFar = 0.0;


		for(int p = 0; (pnum[p] != -1 && p < NUM_PATHS); p++)
		{
			if (randomNum <= (path_ratio[p])/psum + sumSoFar)
			{
				*pathNumber = pnum[p];
				//return (mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[1]); //let the finishing loop handle the return statement
				break;
			}

			sumSoFar += (path_ratio[p])/psum;
		}
	}

	int nextRouter = -1;
	for (int w = 0; w < mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].plength; w++)
	{
		if(mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w] == currentRouter)
		{
			for(int k = 0; k < RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].numLinks; k++)
			{
				bool b1 = RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].NextRouter == mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w+1];
				bool b2 = RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].LinkType == WirelessShortcut;
				bool b3 = RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].HasWirelessToken;
				bool b4 = RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].LinkType != WirelessShortcut;

				if(b1 && b2 && !b3)
				{
					return -2;
				}

				if (b1 && b2 && b3)
				{
					tokenPacketCount[(RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].ChannelType-1)]++;

					if(tokenPacketCount[(RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].ChannelType-1)] >= MAX_TOKEN_PACKETS)
					{
						stallToken[(RT[mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w]].Entries[tree_number][k].ChannelType-1)] = true;
					}
				}
			}

			nextRouter = mPath[sourceRouter][destinationRouter][tree_number][*pathNumber].path[w+1];
		}
	}

	return nextRouter;
}

void removeFromLayer(int layer, int rcount, int ccount, int pathnumber)
{
	int i = 0;
	for(i = 1; i < MultiPathLength[rcount][ccount][pathnumber] - 3; i++)
	{
		dependencyLayer[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]]--;
	}
	for(i = 0; i < MultiPathLength[rcount][ccount][pathnumber]; i++)
	{
		if(fBENCHMARK)
			nodeUsage[layer][MultiPathMsg[rcount][ccount][pathnumber][i]] -= fijMatrix[rcount][ccount];
		else
			nodeUsage[layer][MultiPathMsg[rcount][ccount][pathnumber][i]] -= 1;
	}
	numPerLayer[layer]--;
	//pathLayer[rcount][ccount][pathnumber] = -1;
}

bool addToLayer(int layer, int rcount, int ccount, int pathnumber)
{
	int i = 0;
	bool status = true;
	bool only = true;
	//for(i = 1; i < MultiPathLength[rcount][ccount][pathnumber] - 3; i++)
	//{
	//	if(dependencyCannot[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]] == 1)
	//		return false;
	//}
	for(i = 1; i < MultiPathLength[rcount][ccount][pathnumber] - 3; i++)
	{
		dependencyLayer[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]]++;
	}
	for(i = 1; i < MultiPathLength[rcount][ccount][pathnumber] - 3; i++)
	{
		if( dependencyLayer[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]] == 1)
		{
			status = checkDependency(layer, MultiPathMsg[rcount][ccount][pathnumber][i], MultiPathMsg[rcount][ccount][pathnumber][i+1], MultiPathMsg[rcount][ccount][pathnumber][i+2], MultiPathMsg[rcount][ccount][pathnumber][i], MultiPathMsg[rcount][ccount][pathnumber][i+1], 0);
			if(status == false)
			{
				only = true;
				for(int j = 1; j < MultiPathLength[rcount][ccount][pathnumber] - 3; j++)
				{
					if( dependencyLayer[layer][MultiPathMsg[rcount][ccount][pathnumber][j]][MultiPathMsg[rcount][ccount][pathnumber][j+1]][MultiPathMsg[rcount][ccount][pathnumber][j+2]] == 1 && i != j)
					{
						only = false;
					}
				}
	/*			if(only)
				{
					dependencyCannot[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]] = 1;
				}*/
				for(i = 1; i < MultiPathLength[rcount][ccount][pathnumber] - 3; i++)
				{
					dependencyLayer[layer][MultiPathMsg[rcount][ccount][pathnumber][i]][MultiPathMsg[rcount][ccount][pathnumber][i+1]][MultiPathMsg[rcount][ccount][pathnumber][i+2]]--;
				}
				return false;
			}
		}
	}
	for(i = 0; i < MultiPathLength[rcount][ccount][pathnumber]; i++)
	{
		if(fBENCHMARK)
			nodeUsage[layer][MultiPathMsg[rcount][ccount][pathnumber][i]] += fijMatrix[rcount][ccount];
		else
			nodeUsage[layer][MultiPathMsg[rcount][ccount][pathnumber][i]] += 1;
	}

	pathLayer[rcount][ccount][pathnumber] = layer;
	numPerLayer[layer]++;
	return true;
}

bool checkDependency(int layer, int first, int second, int third, int initial, int next, int count)
{
	bool status = true;
	int i = 0;
	if(count == 26)
	{
		return true;
	}
	for(i = numIps; i < (numIps+numSwitches); i++)
	{
		if(connection[third][i] != -1 && i != second)
		{
			if(dependencyLayer[layer][second][third][i] > 0)
			{
				if(third == initial && i == next)
				{
					return false;
				}
				else
				{
					status = checkDependency(layer, second, third, i, initial, next, count+1);
				}
			}
			if(status == false)
			{
				return false;
			}
		}
	}
	return status;
}

int determine_path(int msgNum)
{
	int src = msgs[msgNum].source[0];
	int dest = msgs[msgNum].dest[0];
	int best = -1;
	int best_congestion = -1;
	int congestion = 0;
	int current_node = 0;

	for (int i =0; i < MultiPathTotal[src][dest]; i++)
	{
		if(pathLayer[src][dest][i] != -1)
		{
			for(int k = 0; k < MultiPathLength[src][dest][i]; k++)
			{
				current_node = MultiPathMsg[src][dest][i][k];
				congestion += RT[current_node].commDensity;
			}
			congestion += MultiPathLength[src][dest][i]*2;
			if(best_congestion == -1)
			{
				best_congestion = congestion;
				best = i;
			}
			else if(best_congestion > congestion)
			{
				best_congestion = congestion;
				best = i;
			}
		}
	}
	return best;
}


void layering_lash()
{
	int pathnumber = 0;
	int *maxPerLayer;
	maxPerLayer = (int *) calloc(numLayers, sizeof(int));
	int rcount = 0;
	int ccount = 0;
	int helpmeout = 0;
	int pcount = 0;
	int ignore = 0;
	int numWirelessPaths = 0;
	for(rcount = 0; rcount < numIps; rcount++)
	{
		for(ccount = 0; ccount < numIps; ccount++)
		{
			if(MultiPathLength[rcount][ccount][0] > MultiPathLength[rcount][ccount][1])
				numWirelessPaths++;
		}
	}
	if(fSTART)
	{	
		//Initial Layering step
		if(fBENCHMARK)
		{
			bool **pathsLayered;
			bool result = false;
			double threshold = 0;
			bool redo = true;
			pathsLayered = (bool **) calloc(numIps, sizeof(bool*));
			for(int i = 0; i < numIps; i++)
			{
				pathsLayered[i] = (bool *) calloc(numIps, sizeof(bool));
			}

			int total_num_paths = 0;

			for (int rcount = 0; rcount < numIps; rcount++)
			{
				for(int ccount = 0; ccount < numIps; ccount++)
				{
					for (int i = 0 ; i < maxPaths; i++)
					{
						if(MultiPathLength[rcount][ccount][i] > 0)
							total_num_paths++;
					}

				}

			}

			int highest = -1;

			while(redo)
			{
				for(int z = 0; z < 10; z++)
				{
					for(int i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsLayered[i][j] = false;
						}
					}
					redo = false;
					for(int p = 0; p < numIps*(numIps - 1); p++)
					{
						highest = -1;
						for (int q = 0; q < numIps; q++)
						{
							for (int r = 0; r < numIps; r++)
							{
								if(q != r)
								{
									if((highest == -1 || fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r]) && pathsLayered[q][r] == false)
									{
										highest = q*numIps + r;
									}
								}
							}
						}
						int bestLayer =  0;
						int bestLayerUsage = 1000000;
						int highestUsage = 0;
						int *layerChecked;
						int startLayer = 0;
						rcount = highest/numIps;
						ccount = highest%numIps;
						pathsLayered[rcount][ccount] = true;
						layerChecked = (int *) calloc(numLayers, sizeof(int));
						for(int i = 0; i < numLayers; i++)
						{
							layerChecked[i] = 0;
						}
						if(MultiPathLength[rcount][ccount][0] > 0)
						{
							for(int k = 0; k < numLayers; k++)
							{
								if(threshold < fijMatrix[rcount][ccount])
									startLayer = rand()%numLayers;
								else
									startLayer = 0;
								for(int i = 0; i < numLayers; i++)
								{
									if(threshold < fijMatrix[rcount][ccount])
									{
										if(layerChecked[(startLayer+i)%numLayers] == 0)
										{
											highestUsage = 0;
											bestLayerUsage = 1000000;
											for(int s = 0; s < MultiPathLength[rcount][ccount][0]; s++)
											{
												if(highestUsage < nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][0][s]])
												{
													highestUsage = nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][0][s]];
												}
											}
											if(highestUsage < bestLayerUsage)
											{
												bestLayer = (startLayer+i)%numLayers;
												bestLayerUsage = highestUsage;
											}
										}
									}
									else
									{
										bestLayer = (startLayer+i)%numLayers;
										if(layerChecked[bestLayer] == 0)
											break;
									}
								}
								result = addToLayer(bestLayer, rcount, ccount, 0);
								layerChecked[bestLayer] = 1;
								if(result == true)
									break;
							}

							if(result == false)
							{
								cout << "Did: " << p << " Threshold: " << threshold << endl;
								cantAdd << "Did: " << p << endl;

								redo = true;
								pathsLayered[rcount][ccount] = false;
								for(int i = 0; i < numIps; i++)
								{
									for(int k = 0 ; k < numIps; k++)
									{
										if(pathsLayered[i][k] == true)
										{
											for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
											{
												if(MultiPathLength[i][k][pathnumber] > 0)
													removeFromLayer(pathLayer[i][k][pathnumber], i, k, pathnumber);
											}
										}
									}
								}

							}
						}
						if(fWIRELESS)
						{
						if(redo == false && MultiPathLength[rcount][ccount][wirelessPathNum] > 0)
						{
							for(int i = 0; i < numLayers; i++)
							{
								layerChecked[i] = 0;
							}
							for(int k = 0; k < numLayers; k++)
							{
								if(threshold < fijMatrix[rcount][ccount])
									startLayer = rand()%numLayers;
								else
									startLayer = 0;
								for(int i = 0; i < numLayers; i++)
								{
									if(threshold < fijMatrix[rcount][ccount])
									{
										if(layerChecked[(startLayer+i)%numLayers] == 0)
										{
											highestUsage = 0;
											bestLayerUsage = 1000000;
											for(int s = 0; s < MultiPathLength[rcount][ccount][wirelessPathNum]; s++)
											{
												if(highestUsage < nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][wirelessPathNum][s]])
												{
													highestUsage = nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][wirelessPathNum][s]];
												}	
											}
											if(highestUsage < bestLayerUsage)
											{
												bestLayer = (startLayer+i)%numLayers;
												bestLayerUsage = highestUsage;
											}
										}
									}	
									else
									{
										bestLayer = (startLayer+i)%numLayers;
										if(layerChecked[bestLayer] == 0)
											break;
									}
								}
								result = addToLayer(bestLayer, rcount, ccount, wirelessPathNum);
								layerChecked[bestLayer] = 1;
								if(result == true)
									break;
							}

							if(result == false)
							{
								cout << "Did: " << p << " Threshold: " << threshold << endl;
								cantAdd << "Did: " << p << endl;

								redo = true;
								pathsLayered[rcount][ccount] = false;
								if(MultiPathLength[rcount][ccount][0] > 0)
									removeFromLayer(pathLayer[rcount][ccount][0], rcount, ccount, 0);
								for(int i = 0; i < numIps; i++)
								{
									for(int k = 0 ; k < numIps; k++)
									{
										if(pathsLayered[i][k] == true)
										{
											for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
											{
												if(MultiPathLength[i][k][pathnumber] > 0)
													removeFromLayer(pathLayer[i][k][pathnumber], i, k, pathnumber);
											}
										}
									}
								}

							}
						}
						}
						if(redo)
							break;
					}
					if(redo == false)
						break;
				}
				threshold += (fijAverage*0.1);
			}

			double layerMetric[4] = {0,0,0,0};

			for(int rcount = 0; rcount < numIps; rcount++)
			{
				for(int ccount = 0; ccount < numIps; ccount++)
				{
					for(int i = 0; i < maxPaths; i++)
					{
						if(MultiPathLength[rcount][ccount][i] > 0)
						{
							layerMetric[pathLayer[rcount][ccount][i]] += (MultiPathLength[rcount][ccount][i]-2)*fijMatrix[rcount][ccount];
						}
					}
				}
			}

			for(int i = 0 ; i < numLayers; i++)
			{
				layerMetric[i] /= numIps;
			}


			
			int *layerChecked;
			layerChecked = (int *) calloc(numLayers, sizeof(int));
			for(int i = 0; i < numIps; i++)
			{
				pathsLayered[i] = (bool *) calloc(numIps, sizeof(bool));
			}

			for(int z = 0; z < 10; z++)
			{
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						pathsLayered[i][j] = false;
					}
				}
				for(int p = 0; p < numIps*(numIps - 1); p++)
				{
					highest = -1;
					for (int q = 0; q < numIps; q++)
					{
						for (int r = 0; r < numIps; r++)
						{
							if(q != r)
							{
								if(highest == -1)
								{
									if(pathsLayered[q][r] == false)
										highest = q*numIps + r;
								}
								else
								{
									if(fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r] && pathsLayered[q][r] == false)
										highest = q*numIps + r;
								}
							}
						}
					}
					int bestLayer =  0;
					double bestLayerUsage = 1000000;
					int highestUsage = 0;

					int startLayer = 0;
					rcount = highest/numIps;
					ccount = highest%numIps;
					pathsLayered[rcount][ccount] = true;

					int total_num_paths = 0;

					int layerInit = pathLayer[rcount][ccount][0];
					double highest[4] = {0,0,0,0};
					if(layerInit != -1)
					{
						for(int i = 0; i < numLayers; i++)
						{
							layerChecked[i] = 0;
						}
						for(int i = 0; i < numLayers; i++)
						{
							for(int k = 0; k < MultiPathLength[rcount][ccount][0]; k++)
							{
								if(highest[i] < nodeUsage[i][MultiPathMsg[rcount][ccount][0][k]])
								{
									highest[i] = nodeUsage[i][MultiPathMsg[rcount][ccount][0][k]];
								}
							}
						}
						for(int j = 0; j < (numLayers-1);j++)
						{
							bestLayer = -1;
							bestLayerUsage = 100000;
							for(int i = 0; i < numLayers; i++)
							{
								if(layerChecked[i] == 0 && layerInit != i)
								{
									if(bestLayer == -1)
									{
										bestLayer = i;
										bestLayerUsage = highest[i];
									}
									else if(bestLayerUsage > highest[i])
									{
										bestLayer = i;
										bestLayerUsage = highest[i];
									}

								}
							}
							layerChecked[bestLayer] = 1;
							if((bestLayerUsage + fijMatrix[rcount][ccount]) < highest[layerInit])
							{
								result = addToLayer(bestLayer, rcount, ccount, 0);
								if(result == true)
								{
									removeFromLayer(layerInit, rcount, ccount, 0);
									break;
								}
							}
							else
								break;
						}
					}
					if(fWIRELESS)
					{
						layerInit = pathLayer[rcount][ccount][wirelessPathNum];
						if(layerInit != -1)
						{
							for(int i = 0; i < numLayers; i++)
							{
								layerChecked[i] = 0;
							}
							for(int i = 0; i < numLayers; i++)
							{
								for(int k = 0; k < MultiPathLength[rcount][ccount][wirelessPathNum]; k++)
								{
									if(highest[i] < nodeUsage[i][MultiPathMsg[rcount][ccount][wirelessPathNum][k]])
									{
										highest[i] = nodeUsage[i][MultiPathMsg[rcount][ccount][wirelessPathNum][k]];
									}
								}
							}
							for(int j = 0; j < (numLayers-1);j++)
							{
								bestLayer = -1;
								bestLayerUsage = 100000;
								for(int i = 0; i < numLayers; i++)
								{
									if(layerChecked[i] == 0 && layerInit != i)
									{
										if(bestLayer == -1)
										{
											bestLayer = i;
											bestLayerUsage = highest[i];
										}
										else if(bestLayerUsage > highest[i])
										{
											bestLayer = i;
											bestLayerUsage = highest[i];
										}

									}
								}
								layerChecked[bestLayer] = 1;
								if((bestLayerUsage + fijMatrix[rcount][ccount]) < highest[layerInit])
								{
									result = addToLayer(bestLayer, rcount, ccount, wirelessPathNum);
									if(result == true)
									{
										removeFromLayer(layerInit, rcount, ccount, wirelessPathNum);
										break;
									}
								}
								else
									break;
							}
						}
					}
				}
			}

			double layerMetric2[4] = {0,0,0,0};

			for(int rcount = 0; rcount < numIps; rcount++)
			{
				for(int ccount = 0; ccount < numIps; ccount++)
				{
					for(int i = 0; i < maxPaths; i++)
					{
						if(MultiPathLength[rcount][ccount][i] > 0)
						{
							layerMetric2[pathLayer[rcount][ccount][i]] += (MultiPathLength[rcount][ccount][i]-2)*fijMatrix[rcount][ccount];
						}
					}
				}
			}

			for(int i = 0 ; i < numLayers; i++)
			{
				layerMetric2[i] /= numIps;
			}

			double layerHotspotMetric[4] = {0,0,0,0};
			int * nodesDone;

			nodesDone = (int *) calloc(numIps, sizeof(int));

			
			for(int k = 0; k < numLayers; k++)
			{
				for(int i = 0; i < numIps; i++)
				{
					nodesDone[i] = 0;
				}
				for(int  i = 0; i < numIps/4; i++)
				{
					int highestNode = -1;
					double highestUsage = 100000;
					for(int j = 0; j < numIps; j++)
					{
						if(nodesDone[j] == 0)
						{
							if(highestNode == -1)
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
							else if(highestUsage < nodeUsage[k][j])
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
						}
					}
					nodesDone[highestNode] = 1;
					layerHotspotMetric[k] += highestUsage;
				}
				layerHotspotMetric[k] /= (numIps/4);
			}


			//END Layer Balancing Step
			ofstream paths_wi("paths_lash_wi.txt");
			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int k = 0; k < maxPaths; k++)
						{
							if(MultiPathLength[i][j][k] > 0)
							{
								for(int m = 0; m < MultiPathLength[i][j][k]; m++)
								{
									paths_wi << MultiPathMsg[i][j][k][m] << " ";
								}
								paths_wi << pathLayer[i][j][k];
								paths_wi << endl;

							}
							else
							{
								paths_wi << "-1" << endl;
							}
						}
					}
				}
			}
			paths_wi.close();
		}
		else //if !fBENCHMARK
		{
			for(int p = 0; p < numIps*(numIps-1)*maxPaths; p++)//121212
			{
				int i = 0;
				rcount = (rand() % numIps);
				ccount = rand() % numIps;
				pathnumber = rand() % maxPaths;
				while(pathsDone[rcount][ccount][pathnumber] == 1 || rcount == ccount)
				{
					rcount = rand() % numIps;
					ccount = rand() % numIps;
					pathnumber = rand() % maxPaths;
				}
				pathsDone[rcount][ccount][pathnumber] = 1;

				if(MultiPathLength[rcount][ccount][pathnumber] == -1)
				{
					ignore++;
					continue;

				}
				bool result = false;
				for(i = 0; i < numLayers; i++)
				{
					for(int r = 0; r < MultiPathLength[rcount][ccount][pathnumber]; r++)
					{
						if(nodeUsage[i][MultiPathMsg[rcount][ccount][pathnumber][r]] > 350)
						{
							result = false;
							break;
						}
						else
							result = true;
					}
					if(result == true)
					{
						result = addToLayer(i, rcount, ccount, pathnumber);
					}
					if(result == true)
					{
						break;
					}
				}
				if(result == false)
				{
					cout << "Could not add: " << rcount << " - " << ccount << " - " << pathnumber << endl;
					cantAdd  << "Could not add: " << rcount << " - " << ccount << " - " << pathnumber << endl;
					cout << "Did: " << (p+(numIps*(numIps-1)*pathnumber)) << endl;
					cantAdd << "Did: " << (p+(numIps*(numIps-1)*pathnumber)) << endl;
					for(i = 0; i < numLayers; i++)
					{
						for(int j = 0; j < currInLayer[i]; j++)
						{
							rcount = pathsInLayer[i][j]/numIps;
							ccount = pathsInLayer[i][j]%numIps;
							removeFromLayer(i, rcount, ccount, pathnumber);
						}
						currInLayer[i] = 0;
					}
					p = -1;
					for(i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsDone[i][j][pathnumber] = 0;
						}
					}
				}
				else
				{
					pathsInLayer[i][currInLayer[i]] = (numIps*numIps*pathnumber + numIps*rcount + ccount);
					currInLayer[i]++;
				}

			}
			//END Initial Layering Step

			if(!fWIRELESS)
			{
				//Layer Balancing Step
				int total_num_paths = 0;

				for(int i = 0; i < numLayers; i++)
				{
					maxPerLayer[i] = currInLayer[i];
					total_num_paths += numPerLayer[i];
				}
				for(int i = 0; i < numLayers; i++)
				{
					int j = 0;
					while(numPerLayer[i] > total_num_paths/numLayers && j < maxPerLayer[i])
					{
						for(int k = (numLayers-1); k > i; k--)
						{
							bool result = false;
							if(numPerLayer[k] <  total_num_paths/numLayers)
							{
								pathnumber = pathsInLayer[i][j]/(numIps*numIps);
								pathsInLayer[i][j] %= (numIps*numIps);
								rcount = pathsInLayer[i][j]/numIps;
								ccount = pathsInLayer[i][j]%numIps;

								for(int r = 0; r < MultiPathLength[rcount][ccount][pathnumber]; r++)
								{
									if(nodeUsage[k][MultiPathMsg[rcount][ccount][pathnumber][r]] > 200)
									{
										result = false;
										break;
									}
									else
										result = true;
								}

								if(result == true)
									result = addToLayer(k, rcount, ccount, pathnumber);
								if(result == true)
								{
									removeFromLayer(i, rcount, ccount, pathnumber );
									break;
								}
							}
						}
						j++;
					}
				}
				//END Layer Balancing Step

				ofstream paths_s("paths_lash.txt");
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						if(i != j)
						{
							if(MultiPathLength[i][j][0] > 0)
							{

								for(int m = 0; m < MultiPathLength[i][j][0]; m++)
								{
									paths_s << MultiPathMsg[i][j][0][m] << " ";
								}
								paths_s << pathLayer[i][j][0];
								paths_s << endl;

							}
							else
							{
								paths_s << "-1" << endl;
							}

						}
					}
				}
				paths_s.close();
			}

			if(fWIRELESS)
			{
				int layer = 0;
				for(rcount = 0; rcount < numIps; rcount++)
				{
					for(ccount = 0; ccount < numIps; ccount++)
					{
						pathsDone[rcount][ccount][1] = 0;
					}
				}

				for(int p = 0; p < numIps*(numIps - 1); p++)
				{
					rcount = rand()%numIps;
					ccount = rand()%numIps;
					while(pathsDone[rcount][ccount][1] == 1 || rcount == ccount)
					{
						rcount = rand() % numIps;
						ccount = rand() % numIps;
					}
					pathsDone[rcount][ccount][1] = 1;
					if(MultiPathLength[rcount][ccount][pathnumber] == -1)
						continue;

					int i = 0;
					for(i = 0; i < MultiPathLength[rcount][ccount][wirelessPathNum]; i++)
					{
						if(connections[MultiPathMsg[rcount][ccount][wirelessPathNum][i]][MultiPathMsg[rcount][ccount][wirelessPathNum][i+1]][0] != 'D')
						{
							layer = pathLayer[MultiPathMsg[rcount][ccount][wirelessPathNum][i]-numIps][ccount][0];
							break;
						}
					}
					if((MultiPathMsg[rcount][ccount][wirelessPathNum][i]-numIps) == rcount)
						continue;
					if(layer == pathLayer[rcount][ccount][1])
					{
						bool result = false;
						for(i= 0; i < numLayers; i++)
						{
							if(i != pathLayer[rcount][ccount][1])
							{
								result = addToLayer(i, rcount, ccount, 1);
								if(result == true)
								{
									removeFromLayer(layer, rcount, ccount, 1);
									break;
								}
							}
						}
						if(i == numLayers)
						{
							cout << "failed: " << rcount << " - " << ccount << endl;
							removeFromLayer(pathLayer[rcount][ccount][1], rcount, ccount, 1);
							pathLayer[rcount][ccount][1] = -1;
						}
					}


				}
				int total_num_paths = 0;

				for(int i = 0; i < numLayers; i++)
				{
					maxPerLayer[i] = currInLayer[i];
					total_num_paths += numPerLayer[i];
				}
				for(int i = 0; i < numLayers; i++)
				{
					int j = 0;
					while(numPerLayer[i] > total_num_paths/numLayers && j < maxPerLayer[i])
					{
						for(int k = (numLayers-1); k > i; k--)
						{
							bool result = false;
							if(numPerLayer[k] <  total_num_paths/numLayers)
							{
								pathnumber = pathsInLayer[i][j]/(numIps*numIps);
								pathsInLayer[i][j] %= (numIps*numIps);
								rcount = pathsInLayer[i][j]/numIps;
								ccount = pathsInLayer[i][j]%numIps;

								if(pathnumber == 1)
									continue;

								for(int r = 0; r < MultiPathLength[rcount][ccount][pathnumber]; r++)
								{
									if(nodeUsage[k][MultiPathMsg[rcount][ccount][pathnumber][r]] > 160)
									{
										result = false;
										break;
									}
									else
										result = true;
								}

								if(result == true)
									result = addToLayer(k, rcount, ccount, pathnumber);
								if(result == true)
								{
									removeFromLayer(i, rcount, ccount, pathnumber );
									break;
								}
							}
						}
						j++;
					}
				}
				//END Layer Balancing Step


				ofstream paths_wi("paths_lash_wi.txt");
				for(int i = 0; i < numIps; i++)
				{
					for(int j = 0; j < numIps; j++)
					{
						if(i != j)
						{
							for(int k = 0; k < maxPaths; k++)
							{
								if(MultiPathLength[i][j][k] > 0)
								{
									for(int m = 0; m < MultiPathLength[i][j][k]; m++)
									{
										paths_wi << MultiPathMsg[i][j][k][m] << " ";
									}
									paths_wi << pathLayer[i][j][k];
									paths_wi << endl;

								}
								else
								{
									paths_wi << "-1" << endl;
								}
							}
						}
					}
				}
				paths_wi.close();
			} //END fWIRELESS
		}
	} //END fSTART
	else //IF !fSTART
	{
		int input = -1;
		if(fWIRELESS)
		{
			for(int i = 0; i < channel_1_nodes; i++)
			{
				for(int j = i; j < channel_1_nodes; j++)
				{
					if(i != j)
					{
						connections[channel_1_node[i]][channel_1_node[j]][0] = '1';
						connections[channel_1_node[j]][channel_1_node[i]][0] = '1';
						connection[channel_1_node[i]][channel_1_node[j]] = 10;
						connection[channel_1_node[j]][channel_1_node[i]] = 10;
					}
				}
			}
			for(int i = 0; i < channel_2_nodes; i++)
			{
				for(int j = i; j < channel_2_nodes; j++)
				{
					if(i != j)
					{
						connections[channel_2_node[i]][channel_2_node[j]][0] = '2';
						connections[channel_2_node[j]][channel_2_node[i]][0] = '2';
						connection[channel_2_node[i]][channel_2_node[j]] = 10;
						connection[channel_2_node[j]][channel_2_node[i]] = 10;
					}
				}
			}
			for(int i = 0; i < channel_3_nodes; i++)
			{
				for(int j = i; j < channel_3_nodes; j++)
				{
					if(i != j)
					{
						connections[channel_3_node[i]][channel_3_node[j]][0] = '3';
						connections[channel_3_node[j]][channel_3_node[i]][0] = '3';
						connection[channel_3_node[i]][channel_3_node[j]] = 10;
						connection[channel_3_node[j]][channel_3_node[i]] = 10;
					}
				}
			}
			ifstream paths_wi;
			if(!paths_wi.is_open())
			{
				paths_wi.open("paths_lash_wi.txt", fstream::in);
			}
			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int k = 0; k < maxPaths; k++)
						{
							int l = 0;
							input = -2;
							paths_wi >> input;
							while(input != j && input != -1)
							{
								MultiPathMsg[i][j][k][l++] = input;
								paths_wi >> input;
							}
							if( l == 0)
								MultiPathLength[i][j][k] = -1;
							else
							{
								MultiPathLength[i][j][k] = l;
								paths_wi >> pathLayer[i][j][k];
							}
						}
					}
				}
			}
			paths_wi.close();
		} //END fWIRELESS
		else //IF !fWIRELESS
		{
			ifstream paths_lash;
			if(!paths_lash.is_open())
			{
				paths_lash.open("paths_lash.txt", fstream::in);
			}
			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int k = 0; k < maxPaths; k++)
						{
							int l = 0;
							input = -1;
							while(input != j)
							{
								paths_lash >> input;
								MultiPathMsg[i][j][k][l++] = input;
							}
							MultiPathLength[i][j][k] = l;
							paths_lash >> pathLayer[i][j][k];
						}
					}
				}
			}
			paths_lash.close();
		} //END !fWIRELESS
	} //END !fSTART
}

void layering_alash()
{
	int pathnumber = 0;
	int *maxPerLayer;
	maxPerLayer = (int *) calloc(numLayers, sizeof(int));
	int rcount = 0;
	int ccount = 0;
	int helpmeout = 0;
	int pcount = 0;
	int ignore = 0;

	pathAllocLayer = (int ****) calloc(numIps, sizeof(int ***));
	for(int i = 0; i < numIps; i++)
	{
		pathAllocLayer[i] = (int ***) calloc(numIps, sizeof(int **));
		for(int j = 0; j < numIps; j++)
		{
			pathAllocLayer[i][j] = (int **) calloc(maxPaths, sizeof(int *));
			for(int k = 0; k < maxPaths; k++)
			{
				pathAllocLayer[i][j][k] = (int *) calloc(numLayers, sizeof( int));
				for(int l = 0; l < numLayers; l++)
				{
					pathAllocLayer[i][j][k][l] = 0;
				}
			}
		}
	}
	if(fSTART)
	{	//Initial Layering step
		if(fBENCHMARK && fVIRTDIST)
		{
			bool **pathsLayered;
			bool result = false;
			double threshold = 0;
			bool redo = true;
			pathsLayered = (bool **) calloc(numIps, sizeof(bool*));
			for(int i = 0; i < numIps; i++)
			{
				pathsLayered[i] = (bool *) calloc(numIps, sizeof(bool));
			}

			int highest = -1;
			int *layerChecked;
			int above_threshold = 0;
			layerChecked = (int *) calloc(numLayers, sizeof(int));

			while(redo)
			{
				for(int z = 0; z < 10; z++)
				{
					for(int i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsLayered[i][j] = false;
						}
					}
					redo = false;
					above_threshold = 0;
					for(int p = 0; p < numIps*(numIps - 1); p++)
					{
						highest = -1;
						for (int q = 0; q < numIps; q++)
						{
							for (int r = 0; r < numIps; r++)
							{
								if(q != r)
								{
									if((highest == -1 || fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r]) && pathsLayered[q][r] == false)
									{
										highest = q*numIps + r;
									}
								}
							}
						}
						int bestLayer =  0;
						int bestLayerUsage = 1000000;
						int highestUsage = 0;
						int startLayer = 0;
						
						rcount = highest/numIps;
						ccount = highest%numIps;
						pathsLayered[rcount][ccount] = true;
						if(threshold < fijMatrix[rcount][ccount])
							above_threshold++;

						for (int j = 0 ; j < maxPaths; j++)
						{
							if(MultiPathLength[rcount][ccount][j] > 0)
							{
								for(int i = 0; i < numLayers; i++)
								{
									layerChecked[i] = 0;
								}
								for(int k = 0; k < numLayers; k++)
								{
									if(threshold < fijMatrix[rcount][ccount])
										startLayer = rand()%numLayers;
									else
										startLayer = 0;
									for(int i = 0; i < numLayers; i++)
									{
										if(threshold < fijMatrix[rcount][ccount])
										{
											if(layerChecked[(startLayer+i)%numLayers] == 0)
											{
												highestUsage = 0;
												bestLayerUsage = 1000000;
												for(int s = 0; s < MultiPathLength[rcount][ccount][j]; s++)
												{
													if(highestUsage < nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][j][s]])
													{
														highestUsage = nodeUsage[(startLayer+i)%numLayers][MultiPathMsg[rcount][ccount][j][s]];
													}
												}
												if(highestUsage < bestLayerUsage)
												{
													bestLayer = (startLayer+i)%numLayers;
													bestLayerUsage = highestUsage;
												}
											}
										}
										else
										{
											bestLayer = (startLayer+i)%numLayers;
											if(layerChecked[bestLayer] == 0)
												break;
										}
									}
									result = addToLayer(bestLayer, rcount, ccount, j);
									layerChecked[bestLayer] = 1;
									if(result == true)
									{
										pathAllocLayer[rcount][ccount][j][bestLayer] = 1;
										break;
									}
								}

								if(result == false)
								{
									cout << "Did: " << p << " Threshold: " << threshold << " Above: " << above_threshold <<  endl;

									redo = true;
									pathsLayered[rcount][ccount] = false;
									for(rcount = 0; rcount < numIps; rcount++)
									{
										for(ccount = 0 ; ccount < numIps; ccount++)
										{
											for(pathnumber = 0; pathnumber < maxPaths; pathnumber++)
											{
												for(int i = 0; i < numLayers; i++)
												{
													if(pathAllocLayer[rcount][ccount][pathnumber][i] == 1)
														removeFromLayer(i, rcount, ccount, pathnumber);
													pathAllocLayer[rcount][ccount][pathnumber][i] = 0;
												}
											}
										}
									}

								}
							}
							if(redo)
								break;
						}
						if(redo)
							break;
					}
					if(redo == false)
					{
						for(rcount = 0; rcount < numIps; rcount++)
						{
							for(ccount = 0 ; ccount < numIps; ccount++)
							{
								if(rcount != ccount)
								{
									if (pathsLayered[rcount][ccount] == false)
										cout << "something went wrong" << endl;
								}
							}
						}
						break;
					}
				}
				threshold += (fijAverage*0.1);
			}

			double layerMetric[4] = {0,0,0,0};

			for(int rcount = 0; rcount < numIps; rcount++)
			{
				for(int ccount = 0; ccount < numIps; ccount++)
				{
					for(int i = 0; i < maxPaths; i++)
					{
						if(MultiPathLength[rcount][ccount][i] > 0)
						{
							layerMetric[pathLayer[rcount][ccount][i]] += (MultiPathLength[rcount][ccount][i]-2)*fijMatrix[rcount][ccount];
						}
					}
				}
			}

			double layerMetric2[4] = {0,0,0,0};

			for(int i = 0 ; i < numLayers; i++)
			{
				layerMetric[i] /= numIps;
			}

			for(int i = 0; i < numIps; i++)
			{
				pathsLayered[i] = (bool *) calloc(numIps, sizeof(bool));
			}

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					pathsLayered[i][j] = false;
				}
			}

				for(int p = 0; p < numIps*(numIps - 1); p++)
				{
					highest = -1;
					for (int q = 0; q < numIps; q++)
					{
						for (int r = 0; r < numIps; r++)
						{
							if(q != r)
							{
								if(highest == -1)
								{
									if(pathsLayered[q][r] == false)
										highest = q*numIps + r;
								}
								else
								{
									if(fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r] && pathsLayered[q][r] == false)
										highest = q*numIps + r;
								}
							}
						}
					}
					int bestLayer =  0;
					double bestLayerUsage = 1000000;
					int highestUsage = 0;

					int startLayer = 0;
					rcount = highest/numIps;
					ccount = highest%numIps;
					pathsLayered[rcount][ccount] = true;

					int total_num_paths = 0;

					for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
					{
						if(MultiPathLength[rcount][ccount][pathnumber] > 0)
						{
							for(int i = 0; i < numLayers; i++)
							{
								if(pathAllocLayer[rcount][ccount][pathnumber][i] == 0)
								{
									result = addToLayer(i, rcount, ccount, pathnumber);
									if(result)
										pathAllocLayer[rcount][ccount][pathnumber][i] =1;
								}
							}
						}
					}
				}

				for(int rcount = 0; rcount < numIps; rcount++)
				{
					for(int ccount = 0; ccount < numIps; ccount++)
					{
						for(int i = 0; i < maxPaths; i++)
						{
							if(MultiPathLength[rcount][ccount][i] > 0)
							{
								for(int j = 0; j < numLayers; j++)
								{
									if(pathAllocLayer[rcount][ccount][i][j] == 1)
									{
										layerMetric2[j] += (MultiPathLength[rcount][ccount][i]-2)*fijMatrix[rcount][ccount];
									}
								}
							}
						}
					}
				}
				for(int i = 0 ; i < numLayers; i++)
				{
					layerMetric2[i] /= numIps;
				}

			double layerHotspotMetric[4] = {0,0,0,0};
			int * nodesDone;

			nodesDone = (int *) calloc(numIps, sizeof(int));

			
			for(int k = 0; k < numLayers; k++)
			{
				for(int i = 0; i < numIps; i++)
				{
					nodesDone[i] = 0;
				}
				for(int  i = 0; i < numIps/4; i++)
				{
					int highestNode = -1;
					double highestUsage = 100000;
					for(int j = 0; j < numIps; j++)
					{
						if(nodesDone[j] == 0)
						{
							if(highestNode == -1)
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
							else if(highestUsage < nodeUsage[k][j])
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
						}
					}
					nodesDone[highestNode] = 1;
					layerHotspotMetric[k] += highestUsage;
				}
				layerHotspotMetric[k] /= (numIps/4);
			}
			//END Layer Balancing Step
		}
		else if(fBENCHMARK && fPRIORITYLAYER)
		{
			bool **pathsLayered;
			bool result = false;
			double threshold = 0;
			bool redo = true;
			pathsLayered = (bool **) calloc(numIps, sizeof(bool*));
			for(int i = 0; i < numIps; i++)
			{
				pathsLayered[i] = (bool *) calloc(numIps, sizeof(bool));
			}

			int highest = -1;
			int *layerChecked;
			bool belowThreshold = false;
			int aboveThreshold = 0;
			layerChecked = (int *) calloc(numLayers, sizeof(int));

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					pathsLayered[i][j] = false;
				}
			}

			//Initial Layering step
			while(redo)
			{
				for(int z = 0; z < 10; z++)
				{
					redo = false;
					belowThreshold = false;
					aboveThreshold = 0;
					for(int i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsLayered[i][j] = false;
						}
					}
					for(int p = 0; p < numIps*(numIps-1); p++)//121212
					{
						int i = 0;
						highest = -1;
						if(!belowThreshold)
						{
							for (int q = 0; q < numIps; q++)
							{
								for (int r = 0; r < numIps; r++)
								{
									if(q != r)
									{
										if((highest == -1 || fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r]) && pathsLayered[q][r] == false)
										{
											highest = q*numIps + r;
										}
									}
								}
							}
							rcount = highest / numIps;
							ccount = highest % numIps;
							aboveThreshold++;
							if(fijMatrix[rcount][ccount] < threshold)
								belowThreshold = true;
						}
						else
						{
							do
							{
								rcount = rand() % numIps;
								ccount = rand() % numIps;
							} while(pathsLayered[rcount][ccount] || rcount == ccount);
						}
						pathsLayered[rcount][ccount] = true;
						bool result = true;
						for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
						{
							if(MultiPathLength[rcount][ccount][pathnumber] > 0)
							{
								for(i = 0; i < numLayers; i++)
								{
									result = true;
									if(result == true)
									{
										result = addToLayer(i, rcount, ccount, pathnumber);
									}
									if(result == true)
									{
										pathAllocLayer[rcount][ccount][pathnumber][i] = 1;
										break;
									}
								}
								if(result == false)
									break;
							}
						}
						if(result == false)
						{
							redo = true;
							if((p+1) == aboveThreshold)
								z = 10;
							
							cout << "Did: " << p << " Threshold: " << threshold << " Above: " << aboveThreshold <<  endl;
							for(rcount = 0; rcount < numIps; rcount++)
							{
								for(ccount = 0 ; ccount < numIps; ccount++)
								{
									for(pathnumber = 0; pathnumber < maxPaths; pathnumber++)
									{
										for(i = 0; i < numLayers; i++)
										{
											if(pathAllocLayer[rcount][ccount][pathnumber][i] == 1)
												removeFromLayer(i, rcount, ccount, pathnumber);
											pathAllocLayer[rcount][ccount][pathnumber][i] = 0;
										}
									}
								}
							}
							break;
						}
					}
					if(redo == false)
					{
						for(rcount = 0; rcount < numIps; rcount++)
						{
							for(ccount = 0 ; ccount < numIps; ccount++)
							{
								if(rcount != ccount)
								{
									if (pathsLayered[rcount][ccount] == false)
										cout << "something went wrong" << endl;
								}
							}
						}
						break;
					}
				}
				threshold += (fijAverage*0.1);
			}
			//END Initial Layering Step
			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					pathsLayered[i][j] = false;
				}
			}
			//START SECOND LAYERING STEP
			for(int p = 0; p < numIps*(numIps-1); p++)//121212
			{
				highest = -1;
				for (int q = 0; q < numIps; q++)
				{
					for (int r = 0; r < numIps; r++)
					{
						if(q != r)
						{
							if((highest == -1 || fijMatrix[highest/numIps][highest%numIps] < fijMatrix[q][r]) && pathsLayered[q][r] == false)
							{
								highest = q*numIps + r;
							}
						}
					}
				}
				rcount = highest / numIps;
				ccount = highest % numIps;
				pathsLayered[rcount][ccount] = true;
				bool result = false;
				for(int pathnumber = 0; pathnumber < maxPaths; pathnumber++)
				{
					if(MultiPathLength[rcount][ccount][pathnumber] > 0)
					{
						int i = 0;
						for (int i = 0; i < numLayers; i++)
						{
							if(pathAllocLayer[rcount][ccount][pathnumber][i] == 1)
								break;
						}
						for(int k = i+1; k < numLayers; k++)
						{
							result = addToLayer(k, rcount, ccount, pathnumber);
							if(result == true)
							{
								pathAllocLayer[rcount][ccount][pathnumber][k] = 1;
							}
						}
					}
				}
			}
		}
		else if(!fBENCHMARK || fUNIFORMDIST)//if !fBENCHMARK
		{		
			pathnumber = 0;
			//Initial Layering step
			for(int p = 0; p < numIps*(numIps-1)*maxPaths; p++)//121212
			{
				int i = 0;
				rcount = (rand() % numIps);
				ccount = rand() % numIps;
				pathnumber = rand() % maxPaths;
				while(pathsDone[rcount][ccount][pathnumber] == 1 || rcount == ccount)
				{
					rcount = rand() % numIps;
					ccount = rand() % numIps;
					pathnumber = rand() % maxPaths;
				}
				pathsDone[rcount][ccount][pathnumber] = 1;

				if(MultiPathLength[rcount][ccount][pathnumber] == -1)//> MultiPathLength[rcount][ccount][0])
				{
					MultiPathLength[rcount][ccount][pathnumber] = -1;
					continue;
				}

				bool result = false;
				for(i = 0; i < numLayers; i++)
				{
					result = true;
					if(result == true)
					{
						result = addToLayer(i, rcount, ccount, pathnumber);
					}
					if(result == true)
					{
						pathAllocLayer[rcount][ccount][pathnumber][i] = 1;
						break;
					}
				}
				if(result == false)
				{
					cout << "Could not add: " << rcount << " - " << ccount << " - " << pathnumber << endl;
					cantAdd  << "Could not add: " << rcount << " - " << ccount << " - " << pathnumber << endl;
					cout << "Did: " << (p+(numIps*(numIps-1)*pathnumber)) << endl;
					cantAdd << "Did: " << (p+(numIps*(numIps-1)*pathnumber)) << endl;
					for(i = 0; i < numLayers; i++)
					{
						for(int j = 0; j < currInLayer[i]; j++)
						{
							pathnumber = pathsInLayer[i][j]/(numIps*numIps);
							pathsInLayer[i][j] %= (numIps*numIps);
							rcount = pathsInLayer[i][j]/numIps;
							ccount = pathsInLayer[i][j]%numIps;
							removeFromLayer(i, rcount, ccount, pathnumber);
						}
						currInLayer[i] = 0;
					}
					p = -1;
					for(i = 0; i < numIps; i++)
					{
						for(int j = 0; j < numIps; j++)
						{
							pathsDone[i][j][pathnumber] = 0;
						}
					}
				}
				else
				{
					pathsInLayer[i][currInLayer[i]] = (numIps*numIps*pathnumber + numIps*rcount + ccount);
					currInLayer[i]++;
				}
			}
			//END Initial Layering Step
			
			int *** doing;
			doing = (int ***) calloc(numIps, sizeof(int **));
			for(int i = 0 ; i < numIps; i++)
			{
				doing[i] = (int **) calloc(numIps, sizeof(int *));
				for(int j = 0; j < numIps; j++)
				{
					doing[i][j] = (int *) calloc(maxPaths, sizeof(int ));
					for(int k = 0; k < maxPaths; k++)
					{
						doing[i][j][k] = 0;
					}
				}
			}
			//START SECOND LAYERING STEP
			for(int i = numLayers - 2; i >= 0; i--)
			{
				for(int j = 0; j < currInLayer[i]; j++)
				{
					pathnumber = pathsInLayer[i][j]/(numIps*numIps);
					pathsInLayer[i][j] %= (numIps*numIps);
					rcount = pathsInLayer[i][j]/numIps;
					ccount = pathsInLayer[i][j]%numIps;
					doing[rcount][ccount][pathnumber] = 1;
					bool result = false;
					for(int k = i+1; k < numLayers; k++)
					{
						result = addToLayer(k, rcount, ccount, pathnumber);
						if(result == true)
						{
							pathAllocLayer[rcount][ccount][pathnumber][k] = 1;
						}
					}
				}
			}
			//END SECOND LAYERING STEP

			double layerMetric2[4] = {0,0,0,0};
			for(int rcount = 0; rcount < numIps; rcount++)
				{
					for(int ccount = 0; ccount < numIps; ccount++)
					{
						for(int i = 0; i < maxPaths; i++)
						{
							if(MultiPathLength[rcount][ccount][i] > 0)
							{
								for(int j = 0; j < numLayers; j++)
								{
									if(pathAllocLayer[rcount][ccount][i][j] == 1)
									{
										layerMetric2[j] += (MultiPathLength[rcount][ccount][i]-2)*fijMatrix[rcount][ccount];
									}
								}
							}
						}
					}
				}
				for(int i = 0 ; i < numLayers; i++)
				{
					layerMetric2[i] /= numIps;
				}

			double layerHotspotMetric[4] = {0,0,0,0};
			int * nodesDone;

			nodesDone = (int *) calloc(numIps, sizeof(int));

			
			for(int k = 0; k < numLayers; k++)
			{
				for(int i = 0; i < numIps; i++)
				{
					nodesDone[i] = 0;
				}
				for(int  i = 0; i < numIps/4; i++)
				{
					int highestNode = -1;
					double highestUsage = 100000;
					for(int j = 0; j < numIps; j++)
					{
						if(nodesDone[j] == 0)
						{
							if(highestNode == -1)
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
							else if(highestUsage < nodeUsage[k][j])
							{
								highestNode = j;
								highestUsage = nodeUsage[k][j];
							}
						}
					}
					nodesDone[highestNode] = 1;
					layerHotspotMetric[k] += highestUsage;
				}
				layerHotspotMetric[k] /= (numIps/4);
			}
		}

		if(fWIRELESS)
		{
			ofstream paths_alashwi(path_filename);

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int l = 0; l < maxPaths; l++)
						{
							if(MultiPathLength[i][j][l] != -1)
							{
								for(int m = 0; m < MultiPathLength[i][j][l]; m++)
								{
									paths_alashwi << MultiPathMsg[i][j][l][m] << " ";
								}
								for(int k = 0; k < numLayers; k++)
								{
									if(pathAllocLayer[i][j][l][k] == 1)
										paths_alashwi << k << " ";
								}
							}
							paths_alashwi << "-1";
							paths_alashwi << endl;
						}
					}
				}
			}
			paths_alashwi.close();
		}
		else
		{
			ofstream paths_alash("paths_alash.txt");

			for(int i = 0; i < numIps; i++)
			{
				for(int j = 0; j < numIps; j++)
				{
					if(i != j)
					{
						for(int l = 0; l < maxPaths; l++)
						{
							if(l == 0 || MultiPathLength[i][j][0] == MultiPathLength[i][j][1])
							{
								for(int m = 0; m < MultiPathLength[i][j][l]; m++)
								{
									paths_alash << MultiPathMsg[i][j][l][m] << " ";
								}
								for(int k = 0; k < numLayers; k++)
								{
									if(pathAllocLayer[i][j][l][k] == 1)
										paths_alash << k << " ";
								}
							}
							paths_alash << "-1";
							paths_alash << endl;
						}
					}
				}
			}
			paths_alash.close();
		}
	} //END fSTART
	else //IF !fSTART
	{
		int input = -1;
		ifstream paths_alash;
		if(!paths_alash.is_open())
		{
			if(!fWIRELESS)
				paths_alash.open("paths_alash.txt", fstream::in);
			else
				paths_alash.open(path_filename, fstream::in);
		}
		for(int i = 0; i < numIps; i++)
		{
			for(int j = 0; j < numIps; j++)
			{
				if(i != j)
				{
					for(int k = 0; k < maxPaths; k++)
					{
						int l = 0;
						input = -1;
						paths_alash >> input;
						if(input != -1)
						{
							while(input != j)
							{
								MultiPathMsg[i][j][k][l++] = input;
								paths_alash >> input;
							}
							MultiPathMsg[i][j][k][l++] = input;
							MultiPathLength[i][j][k] = l;

							if(l == 0)
								MultiPathLength[i][j][k] = -1;

							paths_alash >> input;
							while(input != -1)
							{
								pathAllocLayer[i][j][k][input] = 1;
								paths_alash >> input;
							}
						}
					}
				}
			}
		}
		paths_alash.close();
	} //END !fSTART
}

void initialize_benchmarks()
{
	ifstream benchmark_file;

	fijMatrix = (double **) calloc(numIps, sizeof(double *));
	fijMatrixSum = (double *) calloc(numIps, sizeof(double));
	for(int i = 0; i < numIps; i++)
	{
		fijMatrixSum[i] = 0;
		fijMatrix[i] = (double *) calloc(numIps, sizeof(double));
		for(int j = 0; j < numIps; j++)
		{
			fijMatrix[i][j] = 0;
		}
	}
	if(!benchmark_file.is_open()) // yuchen: traffic file specification
	{
	  if(fFFT)
	    benchmark_file.open("traffic_fft.tsv", fstream::in);
	  else if(fLU)
	    benchmark_file.open("traffic_lu.tsv", fstream::in);
	  else if(fRADIX)
	    benchmark_file.open("traffic_radix.tsv", fstream::in);
	  else if(fWATER)
	    benchmark_file.open("traffic_water.tsv", fstream::in);
	  else if(fCANNEAL)
	    benchmark_file.open("traffic_canneal.tsv", fstream::in);
	  else if(fDEDUP)
	    benchmark_file.open("traffic_dedup.tsv", fstream::in);
	  else if(fFLUIDANIMATE)
	    benchmark_file.open("traffic_fluidanimate.tsv", fstream::in);
	  else if(fVIPS)
	    benchmark_file.open("traffic_vips.tsv", fstream::in);
	  else if (fcombined)
	    benchmark_file.open("traffic_combined.tsv", fstream::in);

		else if(fBODYTRACK)
			benchmark_file.open("traffic_bodytrack.txt", fstream::in);
		else if(fFLUID_wonje)
			benchmark_file.open("traffic_fluid_wonje.txt", fstream::in);
		else if(fVIPS_wonje)
			benchmark_file.open("traffic_VIPS_wonje.txt", fstream::in);
		else if(fSWAPTION)
			benchmark_file.open("traffic_swaption.txt", fstream::in);
		else if(fFREQMINE)
			benchmark_file.open("traffic_freqmine.txt", fstream::in);
		else if(fRADIX10)
			benchmark_file.open("traffic_radix_sat_10.txt", fstream::in);
		else if(fRADIX20)
			benchmark_file.open("traffic_radix_sat_20.txt", fstream::in);
		else if(fRADIX30)
			benchmark_file.open("traffic_radix_sat_30.txt", fstream::in);
		else if(fRADIX40)
			benchmark_file.open("traffic_radix_sat_40.txt", fstream::in);
		else if(fRADIX50)
			benchmark_file.open("traffic_radix_sat_50.txt", fstream::in);
		else if(fRADIX60)
			benchmark_file.open("traffic_radix_sat_60.txt", fstream::in);
		else if(fRADIX70)
			benchmark_file.open("traffic_radix_sat_70.txt", fstream::in);
		else if(fRADIX80)
			benchmark_file.open("traffic_radix_sat_80.txt", fstream::in);
		else if(fRADIX90)
			benchmark_file.open("traffic_radix_sat_90.txt", fstream::in);
		else if(fRADIX100)
			benchmark_file.open("traffic_radix_sat_100.txt", fstream::in);
		else if(fBODYTRACK10)
			benchmark_file.open("traffic_bodytrack_sat_10.txt", fstream::in);
		else if(fBODYTRACK20)
			benchmark_file.open("traffic_bodytrack_sat_20.txt", fstream::in);
		else if(fBODYTRACK30)
			benchmark_file.open("traffic_bodytrack_sat_30.txt", fstream::in);
		else if(fBODYTRACK40)
			benchmark_file.open("traffic_bodytrack_sat_40.txt", fstream::in);
		else if(fBODYTRACK50)
			benchmark_file.open("traffic_bodytrack_sat_50.txt", fstream::in);
		else if(fBODYTRACK60)
			benchmark_file.open("traffic_bodytrack_sat_60.txt", fstream::in);
		else if(fBODYTRACK70)
			benchmark_file.open("traffic_bodytrack_sat_70.txt", fstream::in);
		else if(fBODYTRACK80)
			benchmark_file.open("traffic_bodytrack_sat_80.txt", fstream::in);
		else if(fBODYTRACK90)
			benchmark_file.open("traffic_bodytrack_sat_90.txt", fstream::in);
		else if(fBODYTRACK100)
			benchmark_file.open("traffic_canneal_sat_100.txt", fstream::in);
		else if(fCANNEAL10)
			benchmark_file.open("traffic_canneal_sat_10.txt", fstream::in);
		else if(fCANNEAL20)
			benchmark_file.open("traffic_canneal_sat_20.txt", fstream::in);
		else if(fCANNEAL30)
			benchmark_file.open("traffic_canneal_sat_30.txt", fstream::in);
		else if(fCANNEAL40)
			benchmark_file.open("traffic_canneal_sat_40.txt", fstream::in);
		else if(fCANNEAL50)
			benchmark_file.open("traffic_canneal_sat_50.txt", fstream::in);
		else if(fCANNEAL60)
			benchmark_file.open("traffic_canneal_sat_60.txt", fstream::in);
		else if(fCANNEAL70)
			benchmark_file.open("traffic_canneal_sat_70.txt", fstream::in);
		else if(fCANNEAL80)
			benchmark_file.open("traffic_canneal_sat_80.txt", fstream::in);
		else if(fCANNEAL90)
			benchmark_file.open("traffic_canneal_sat_90.txt", fstream::in);
		else if(fCANNEAL100)
			benchmark_file.open("traffic_canneal_sat_100.txt", fstream::in);
	}
	if(benchmark_file.is_open())
	{
		for(int i = 0; i < numIps; i++)
		{
			for(int j = 0; j < numIps; j++)
			{
				benchmark_file >> fijMatrix[i][j];
			}
		}
	}
	else
	{
		cout << "ERROR: ONE OF THE FLAGS HAS NOT BEEN SET" << endl;
		exit(1);
	}
	for(int i = 0; i < numIps; i++)
	{

		fijMatrixSum[i] = 0;
		for(int j = 0; j < numIps; j++)
		{
			messagesInjected[i][j] = 0;
			fijMatrixSum[i] += fijMatrix[i][j];
		}
	}
	double fijTotal = 0;
	fijAverage = 0;
	for(int i = 0; i < numIps; i++)
	{
		for(int j = 0; j < numIps; j++)
		{
			if(i != j)
			{
				fijTotal += fijMatrix[i][j];
			}
		}
	}
	fijAverage = fijTotal / (numIps*(numIps-1));
	
	double half = fijTotal / 2;
	int highest = 0;
	double highestfij = 0;
	double tempTotal = 0;
	int total_done = 0;
	int ** done = (int **) calloc(numIps, sizeof( int *));
	for(int i = 0; i < numIps; i++)
	{
		done[i] = (int *) calloc(numIps, sizeof(int));
		for(int j =0; j < numIps; j++)
		{
			done[i][j] = 0;
		}
	}
	while(tempTotal < half)
	{
		highestfij = 0;
		for(int i = 0; i < numIps; i++)
		{
			for(int j = 0; j < numIps; j++)
			{
				if(i != j)
				{
					if(done[i][j] == 0 && fijMatrix[i][j] > highestfij)
					{
						highest = i*numIps + j;
						highestfij = fijMatrix[i][j];
					}
				}
			}
		}
		total_done++;
		done[highest/numIps][highest%numIps] = 1;
		tempTotal += fijMatrix[highest/numIps][highest%numIps];
	}
	highest = 0;
	highestfij = 0;
	for(int i = 0; i < numIps; i++)
	{
		for(int j = 0; j < numIps; j++)
		{
			if(i != j)
			{
				if(done[i][j] == 0 && fijMatrix[i][j] > highestfij)
				{
					highest = i*numIps + j;
					highestfij = fijMatrix[i][j];
				}
			}
		}
	}
	fij50 = fijMatrix[highest/numIps][highest%numIps];
}




void request_analyses ()
{

	int i,j,temp;
	
	//token 1 request processing
	if (request_count[0]>0)
	{
		temp=last_token_node_index[0];
		//cout<<" Req ana_earlier Cycles: "<<cycles<<" temp: "<<temp<<endl;

		temp=(temp+1)%channel_1_nodes;
		//cout<<" Req ana Cycles: "<<cycles<<" temp: "<<temp<<endl;
		for(i=1;i<=channel_1_nodes;i++)
		{
			if(token_request[channel_1_node[temp]][0]==true)
			{
				token1=channel_1_node[temp];
				free_token[0]=false;
				last_token_node_index[0]=temp;
				for(int j=0;j<channel_1_nodes;j++)
				{
					token_request[channel_1_node[j]][0]=false;
				}
				//cout<<" Req ana2 Cycles: "<<cycles<<" temp: "<<temp<<" requesting node "<<channel_1_node[temp]<<"token1: "<<token1<<""<<endl;

				break;
			}
			else
			{
				temp=(temp+1)%channel_1_nodes;
			}
		}
	}


	//token 2 request processing
	if (request_count[1]>0)
	{
		temp=last_token_node_index[1];
		temp=(temp+1)%channel_2_nodes;
		for(i=1;i<=channel_2_nodes;i++)
		{
			if(token_request[channel_2_node[temp]][1]==true)
			{
				token2=channel_2_node[temp];
				free_token[1]=false;
				last_token_node_index[1]=temp;
				for(int j=0;j<channel_2_nodes;j++)
				{
					token_request[channel_2_node[j]][1]=false;
				}
				//cout<<" Req ana2 Cycles: "<<cycles<<" temp: "<<temp<<" requesting node "<<channel_1_node[temp]<<"token1: "<<token1<<""<<endl;

				break;
			}
			else
			{
				temp=(temp+1)%channel_2_nodes;
			}
		}
	}

	//token 3 request processing
	if (request_count[2]>0)
	{
		temp=last_token_node_index[2];
		temp=(temp+1)%channel_3_nodes;
		for(i=1;i<=channel_3_nodes;i++)
		{
			if(token_request[channel_3_node[temp]][2]==true)
			{
				token3=channel_3_node[temp];
				free_token[2]=false;
				last_token_node_index[2]=temp;
				for(int j=0;j<channel_3_nodes;j++)
				{
					token_request[channel_3_node[j]][2]=false;
				}
				//cout<<" Req ana2 Cycles: "<<cycles<<" temp: "<<temp<<" requesting node "<<channel_1_node[temp]<<"token1: "<<token1<<""<<endl;

				break;
			}
			else
			{
				temp=(temp+1)%channel_3_nodes;
			}
		}
	}

	for(int i=0;i<=2;i++)
	{
		/*if(request_count[0]>0)
		{
			cout<<" Req ana2 Cycles: "<<cycles<<" temp: "<<temp<<" requesting node "<<channel_1_node[temp]<<"token1: "<<token1<<""<<endl;
		}*/
		request_count[i]=0;
	}	

}

void initbenchmark__flags(void)
{
	//fCANNEAL=false;
	//fBODYTRACK=false;
	//fRADIX=false;
//	fFFT=false;
	//fLU=false;
}
