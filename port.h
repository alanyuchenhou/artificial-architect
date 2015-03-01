#ifndef PORT_H
#define PORT_H


class port {


public:

int *o_buff;		// output buffer contents
int *i_buff;		// input buffer contents
int next;		// port at other end of the link
int next_type;
int to_gateway;		// port in direction of the gateway
int last_virt_sent;  // stores the number of the last 
int last_virt_sent_intra;  // stores the number of the last 
bool sent_this_cycle;	// if a flit has advance to the next port from this output buffer
bool sent_this_cycle_intra;	// if a flit has advance to the next port from this output buffer
int delay; //sourav  for TSV failure need 2 cycles to rout the ful flit

// default constructor

port () {
	next = -1;
	next_type = -1;
	sent_this_cycle=false;
	sent_this_cycle_intra=false;
	last_virt_sent=0;
	last_virt_sent_intra=0;
	delay=-1;  //sourav 
}


};
#endif
