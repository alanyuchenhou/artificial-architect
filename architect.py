#!/usr/bin/env python

from os import devnull
from copy import copy
from cProfile import run
from itertools import combinations
from functools import reduce
from operator import mul
from random import uniform
from shlex import split
from time import sleep
from time import strftime
from subprocess import check_call
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
from numpy import asarray
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

class Critic(object):
    def evaluate_kernels(self, dataset):
        data = actuator.load_data(dataset)
        kernels = ['linear', 'poly', 'rbf', 'sigmoid']
        for kernel in kernels:
            svr = SVR(kernel)
            parameters = {'C':logspace(0, 2, 3).tolist()}
            if kernel == 'poly':
                parameters['degree'] = linspace(1, 4, 4, dtype = 'int').tolist()
            if kernel == 'rbf':
                parameters['gamma'] = logspace(-4, 0, 5).tolist()
            estimator = GridSearchCV(svr, parameters, cv = 10, n_jobs = -1)
            estimator.fit(data[2][:-10], data[1][:-10])
            print 'kernel=', kernel,
            print 'best_params=', estimator.best_params_,
            print 'best_score=', estimator.best_score_
class Learner(object):
    DATASET = 'dataset.dat'
    def build_estimators(self, dataset, target_count):
        data = actuator.load_data(dataset)
        c_range = 4
        gamma_range = 4
        parameters = {'C' : logspace(0, c_range-1, c_range).tolist(),
                      'gamma' : logspace(1-gamma_range, 0, gamma_range).tolist()}
        estimators = []
        svrs = []
        for i in range(target_count):
            svrs.append(SVR('rbf'))
            estimators.append(GridSearchCV(svrs[i], parameters, n_jobs = -1))
            estimators[i].fit(data[target_count], data[i])
            print 'best_params=', estimators[i].best_params_,
            print 'best_score=', estimators[i].best_score_
        return estimators

class Performer(object):
    NODE_COUNT = 64
    TARGET_NAMES = ['latency', 'power']
    TARGET_TOKENS = ['Packet latency average = ', '- Total Power:             ']
    TARGET_COUNT = len(TARGET_NAMES)
    TRACE = 'trace.dat'
    estimators = []
    def update_estimators(self, dataset):
        self.estimators = learner.build_estimators(dataset, self.TARGET_COUNT)
    def generate_random_graph(self, degree):
        while True:
            graph = gnm_random_graph(self.NODE_COUNT, self.NODE_COUNT*degree)
            if is_connected(graph):
                return graph
    def extract_features(self, graph):
        features = [number_of_edges(graph), average_shortest_path_length(graph),
                    diameter(graph), radius(graph)]
        return features
    def estimate_targets(self, raw_features):
        raw_sample = asarray(range(self.TARGET_COUNT) + raw_features)
        sample = actuator.scaler.transform(raw_sample)
        targets = []
        for i in range(self.TARGET_COUNT):
            targets += (self.estimators[i].predict(sample[self.TARGET_COUNT:])).tolist()
        return targets
    def evaluate_quality(self, targets):
        return - reduce(mul, targets, 1)
    def build_dataset(self):
        with open(self.TRACE, 'w') as stream:
            print >> stream, 'latency \t power \t edge_count \t path_length \t diameter \t radius'
        for round in range(1000):
            graph = self.generate_random_graph(uniform(2, 16))
            actuator.add_data(graph, self.TARGET_TOKENS, learner.DATASET)

class Sensor(object):
    def extract_targets(self, simulation_log, target_tokens):
        with open(simulation_log, 'r') as stream:
            target_values = copy(target_tokens)
            for line in stream:
                for index in range(len(target_tokens)):
                    if line.startswith(target_tokens[index]):
                        value_string = (line.replace(target_tokens[index], '').partition(' ')[0])
                        target_values[index] = float(value_string)
        return target_values
    
class Actuator(object):
    # TOPOLOGY = 'sw_connection.txt'
    TOPOLOGY = 'booksim2/src/examples/anynet/anynet_file'
    CONFIGURATION = 'booksim2/src/examples/anynet/anynet_config'
    SIMULATOR = 'booksim2/src/booksim'
    SIMULATION_LOG = 'simulation.log'
    scaler = StandardScaler()
    def load_data(self, dataset):
        raw_dataset = loadtxt(dataset)
        self.scaler.fit(raw_dataset)
        scaled_dataset = self.scaler.transform(raw_dataset)
        split_dataset = map(squeeze, hsplit(scaled_dataset,[1,2]))
        return split_dataset
    def add_data(self, graph, target_tokens, dataset):
        connection = to_dict_of_lists(graph)
        with open(self.TOPOLOGY, 'w+') as stream:
            for source in connection:
                destinations = 'router ' + ' router '.join(map(str, connection[source]))
                print >> stream, 'router', source, 'node', source, destinations
        with open(self.SIMULATION_LOG, 'w') as stream:
            check_call([self.SIMULATOR, self.CONFIGURATION], stdout = stream)
        targets = sensor.extract_targets(self.SIMULATION_LOG, target_tokens)
        features = performer.extract_features(graph)
        sample = targets + features
        if dataset == performer.TRACE:
            sample.insert(0, performer.evaluate_quality(targets))
        # raw_sample = self.scaler.inverse_transform(asarray(sample))
        with open(dataset, 'a') as stream:
            print >> stream, '\t'.join(map(str, sample))
    # def simulate(self, args, SIMULATION_LOG):
    #     parameters = [1,8,1,64,11,64,64,5,0,0,4,7,1.8,'s',6,1,1,'r']
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

class Optimization(SearchProblem):
    def actions(self, state):
        actuator.add_data(state, performer.TARGET_TOKENS, performer.TRACE)
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
        raw_features = performer.extract_features(state)
        targets = performer.estimate_targets(raw_features)
        quality = performer.evaluate_quality(targets)
        return quality
    def generate_random_state(self):
        state = performer.generate_random_graph(uniform(2, 16))
        return state

learner = Learner()
performer = Performer()
actuator = Actuator()
sensor = Sensor()
optimization = Optimization()

performer.update_estimators(learner.DATASET)
final = hill_climbing_random_restarts(optimization, 10, 1000)

