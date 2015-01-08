#!/usr/bin/env python

NODE_COUNT = 64
SIMULATION_LOG = 'simulation.log'
DATASET = 'dataset.dat'
TRACE = 'trace.dat'
SIMULATOR = 'booksim2/src/booksim'
TOPOLOGY = 'booksim2/src/examples/anynet/anynet_file'
CONFIGURATION = 'booksim2/src/examples/anynet/anynet_config'

# PREDICTING_LOG = 'predicting.log'
# INSTANCE = 'instance.dat'
# DATABASE = 'database.dat'
# SIMULATOR = 'simulator.out'
# TOPOLOGY = 'sw_connection.txt'

# modify stdout to flush stream after every call
# class Unbuffered(object):
#     def __init__(self, stream):
#         self.stream = stream
#     def write(self, data):
#         self.stream.write(data)
#         self.stream.flush()
#     def __getattr__(self, attr):
#         return getattr(self.stream, attr)
# import sys
# sys.stdout = Unbuffered(sys.stdout)

from sys import exit
from os import devnull
from cProfile import run
from itertools import combinations
from random import uniform
from shlex import split
from time import sleep
from time import strftime
from subprocess import check_call
from subprocess import call
from subprocess import Popen
from subprocess import PIPE
from simpleai.search import SearchProblem
from simpleai.search.local import hill_climbing_random_restarts
from networkx import Graph
from networkx import nodes
from networkx import is_connected
from networkx import average_shortest_path_length
from networkx import diameter
from networkx import number_of_edges
from networkx import radius
from networkx import density
from networkx import draw
from networkx import random_regular_graph
from networkx import gnm_random_graph
from networkx import to_numpy_matrix
from networkx import to_dict_of_lists
from networkx import to_dict_of_dicts
from numpy import loadtxt
from numpy import savetxt
from numpy import arange
from numpy import matrix
from numpy import zeros
from numpy import fill_diagonal
from numpy import vstack
from numpy import hstack
from numpy import hsplit
from numpy import vsplit
from numpy import logspace
from numpy import linspace
from numpy import squeeze
from sklearn import datasets
from sklearn.svm import SVR
from sklearn.svm import SVC
from sklearn.grid_search import GridSearchCV
from sklearn.preprocessing import scale
from sklearn.preprocessing import StandardScaler

# draw(graph1)

class Learner(object):
    def evaluate_kernels(self, DATASET):
        unscaled_dataset = loadtxt(DATASET)
        scaler = StandardScaler()
        scaler.fit(unscaled_dataset)
        dataset = scaler.transform(unscaled_dataset)
        reversed_dataset = scaler.inverse_transform(dataset)
        subdataset = hsplit(dataset,[1])
        kernels = ['linear', 'poly', 'rbf']
        for kernel in kernels:
            svr = SVR(kernel)
            # parameters = {'kernel':[kernel], 'C':logspace(-4, 4, 9).tolist()}
            parameters = {'C':logspace(-2, 2, 5).tolist()}
            if kernel == 'poly':
                parameters['degree'] = linspace(1, 4, 4, dtype = 'int').tolist()
            if kernel == 'rbf':
                parameters['gamma'] = logspace(-4, 4, 9).tolist()
            # print parameters
            regressor = GridSearchCV(svr, parameters, cv = 10, n_jobs = -1)
            regressor.fit(subdataset[1][:-10], squeeze(subdataset[0])[:-10])
            print 'kernel=', kernel,
            print 'best_params=', regressor.best_params_,
            print 'best_score=', regressor.best_score_
            # print regressor.predict(subdataset[1][-10:])
            # print squeeze(subdataset[0][-10:])
    def build_model(self, DATABASE):
        with open(devnull, 'w') as DEVNULL:
            check_call(split('svm_rank_learn -c 10 -l 1 ' + DATABASE + '  model'), stdout = DEVNULL)

class Performer(object):
    def extract_features(self, graph):
        features = []
        features.append(number_of_edges(graph))
        features.append(average_shortest_path_length(graph))
        features.append(diameter(graph))
        features.append(radius(graph))
        return features
    def generate_random_graph(self, edge_count):
        while True:
            graph = gnm_random_graph(NODE_COUNT, edge_count)
            if is_connected(graph):
                return graph
    def assess(self, features):
        data_instance = actuator.combine(-.1, features)
        actuator.write(data_instance, INSTANCE, 'w+')
        with open(PREDICTING_LOG, 'w+') as out:
            check_call(['svm_rank_classify', INSTANCE, 'model', 'predictions'], stdout = out)
        with open('predictions', 'r') as assess_result:
            for line in assess_result:
                return - float(line)
    def build_dataset(self):
        for round in range(1000):
            graph = self.generate_random_graph(NODE_COUNT*uniform(2, 16))
            features = self.extract_features(graph)
            actuator.configure(graph, TOPOLOGY)
            actuator.simulate()
            quality = sensor.extract_targets(graph)
            data_instance = actuator.combine(quality, features)
            actuator.write(data_instance, DATABASE, 'a')

class Sensor(object):
    def extract_targets(self):
        with open(SIMULATION_LOG, 'r') as simulation_log:
            targets = {'latency':{'token': 'Packet latency average = ', 'value' : -1},
                       'power':{'token' : '- Total Power:             ', 'value' : -1}}
            for line in simulation_log:
                for target in targets:
                    if line.startswith(targets[target]['token']):
                        value_string = (line.replace(targets[target]['token'], '').partition(' ')[0])
                        targets[target]['value'] = float(value_string)
        return targets
    
class Actuator(object):
    # def simulate(self, args, SIMULATION_LOG):
    # parameters = [1,8,1,64,11,64,64,5,0,0,4,7,1.8,'s',6,1,1,'r']
    #     # print '################################################################'
    #     print 'actuator.simulate: simulation started'
    #     process1 = Popen([args], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    #     for parameter in self.parameters:
    #         # print 'continue?'
    #         # sys.stdin.readline()
    #         while True:
    #             reply = process1.stdout.readline()
    #             # print 'receiving:', reply,
    #             if reply.partition(' ')[0] == 'Enter':
    #                 break
    #         # print 'actuator.simulate: sending parameter to simulator:', parameter
    #         print >> process1.stdin, parameter
    #         # sleep(.5)
    #     out1, error1 = process1.communicate()
    #     with open(SIMULATION_LOG,'w+') as result:
    #         print >> result, out1
    #     print 'actuator.simulate: simulation finished'
    # def configure(self, graph, TOPOLOGY):
    #     adjacency = to_numpy_matrix(graph,dtype=int)
    #     adjacency *= 2
    #     adjacency += -1
    #     all_disconnected = zeros ((NODE_COUNT, NODE_COUNT),dtype = int)
    #     all_disconnected -= 1
    #     side = all_disconnected.copy()
    #     fill_diagonal(side,2)
    #     configuration = hstack((vstack((all_disconnected, side)), vstack((side, adjacency))))
    #     savetxt(TOPOLOGY, configuration, fmt='%d')
    def simulate(self):
        with open(SIMULATION_LOG, 'w') as log:
            check_call([SIMULATOR, CONFIGURATION], stdout = log)
    def configure(self, graph, TOPOLOGY):
        connection = to_dict_of_lists(graph)
        with open(TOPOLOGY, 'w+') as configuration:
            for source in connection:
                print >> configuration, 'router', source, 'node', source,\
                'router', ' router '.join(map(str, connection[source]))
    def combine(self, score, features):
        data_instance = []
        data_instance.append(str(score))
        data_instance.append('qid:1')
        for index in range(len(features)):
            data_instance.append(str(index+1) + ':' + str(features[index]))
        return data_instance
    # def divide(self, DATABASE): # depreciated
    #     with open('train.dat', 'w+') as out:
    #         check_call(['sed', '-e', '1,10d', DATABASE], stdout = out)
    #     with open('test.dat', 'w+') as out:
    #         check_call(['sed', '-n', '1,10p', DATABASE], stdout = out)
    def write(self, data_instance, DATABASE, mode):
        instance = ' '.join(element for element in data_instance)
        with open(DATABASE, mode) as database:
            print >> database, instance

class Optimization(SearchProblem):
    def actions(self, state):
        features = performer.extract_features(state)
        actuator.configure(state, TOPOLOGY)
        actuator.simulate()
        quality = sensor.extract_targets(state)
        data_instance = actuator.combine(quality, features)
        actuator.write(data_instance, DATABASE, 'a')
        with open(TRACE, 'a') as trace:
            score = performer.assess(features)
            print >> trace, '\t'.join(map(str, [score] + [quality] + features))
        successors = []
        for cluster in combinations(nodes(state),2):
            successor = state.copy()
            for node_pair in combinations(cluster,2):
                if node_pair[0] in successor.neighbors(node_pair[1]):
                    successor.remove_edge(node_pair[0],node_pair[1])
                else:
                    successor.add_edge(node_pair[0],node_pair[1])
            if is_connected(successor):
                successors.append(successor)
        return successors
    def result(self, state, action):
        return action
    def value(self, state):
        features = performer.extract_features(state)
        score = performer.assess(features)
        return score
    def generate_random_state(self):
        with open(TRACE, 'a') as trace:
            print >> trace, 'score \t latency \t edge_count \t path_length \t diameter \t radius'
            graph = performer.generate_random_graph(2*NODE_COUNT)
        # learner.build_model(DATABASE)
        return graph

learner = Learner()
performer = Performer()
actuator = Actuator()
sensor = Sensor()
optimization = Optimization()

# time_stamp = strftime('%Y-%m-%d-%H-%M-%S')
# check_call(['mv', TRACE, TRACE[:5] + '-' + time_stamp + TRACE[5:]])
# final = hill_climbing_random_restarts(optimization, 10, 1000)

# learner.evaluate_kernels(DATASET)
# actuator.simulate()
print sensor.extract_targets()
