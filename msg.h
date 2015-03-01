#ifndef MSG_H
#define MSG_H


class msg {


public:

int *source;
int *dest;
int *path;	// store ports
int *vpath;	//	store virts
int *path_history;
int path_length;
int start_time;
int start_network;
int end_time;
int end_network;
int upper;	// for torus deadlock free routing
int dim;	// holds dimension of travel for message
int num;	// message number
//msg *next;
//msg *prev;
int next_collide;
int prev_collide;
int next;
int prev;
int virt;
int bw;
int priority;
int temp_priority;	// inherited priority
int req_port;		// the next port the header would like to enter
int req_port2;  //The secondary port the header would like to enter for ALASH
bool header_moved;
bool header_done;
bool header_in;		// true if msg header is in an input buffer
bool is_blocked;
int mtree_number;
int global_pathNumber;


bool partialTSVfaced; //sourav
int wait;
int layer;
int layer_history[4];
int pathNum;
bool rerout;
bool wireless;
int sourceOrig;
int sourceRerout;

// default constructor

msg (){
	path_length = 0;
	wireless = false;
	start_time = 0;
	start_network = -1;
	end_time = -1;
	end_network = -1;
	dim =0;
	next_collide = -1;
	prev_collide = -1;
	num = 0;
	next = -1;
	prev = -1;
	virt=-1;
	priority=-1;
	header_moved=false;
	header_done=false;
	header_in=false;
	is_blocked=false;
	bw = 0;
	mtree_number=0;
	wait = -1;
	layer = 0;
	layer_history[0] = 0;
	layer_history[1] = 0;
	layer_history[2] = 0;
	layer_history[3] = 0;
	sourceOrig = -1;
	pathNum = 0;
	rerout = false;
	sourceRerout = -1;
	partialTSVfaced = false; //sourav
}

msg (int levels) {
	dim=0;
	path_length = 0;
}


};
#endif
