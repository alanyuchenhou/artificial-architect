#ifndef IP_H
#define IP_H


class ip {


public:

int *generate;
int *generate_msgs;
int *consume;
int *consume_msgs;
int current_msg;
int *queue;
int queue_pop;
int next_arrival;
int is_on;             // For self-similar traffic
int next_state_change; // For self-similar traffic
int mtree_number;
int *queue_dest;

// default constructor

ip () {
	current_msg=0;
	queue_pop=0;
	next_arrival=-1;
	mtree_number=0;

}


};
#endif
