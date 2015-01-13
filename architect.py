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
from networkx import get_node_attributes
from networkx import get_edge_attributes
from networkx import neighbors
from networkx import is_connected
from networkx import average_shortest_path_length
from networkx import diameter
from networkx import number_of_edges
from networkx import radius
from networkx import density
from networkx import draw
from networkx import draw_networkx_edge_labels
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
        c_range = 8
        gamma_range = 8
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
learner = Learner()

class Performer(object):
    DIMENSION = 2
    RADIX = 4
    NODE_COUNT = RADIX ** 2
    DEGREE_MIN = 1.5
    DEGREE_MAX = 8
    TARGET_NAMES = ['latency', 'power']
    TARGET_TOKENS = ['Packet latency average = ', '- Total Power:             ']
    TARGET_COUNT = len(TARGET_NAMES)
    TRACE = 'trace.dat'
    estimators = []
    def update_estimators(self, dataset):
        names = 'latency_power_product \t latency \t power \t edge_count \t path_length \t diameter \t radius'
        with open(self.TRACE, 'w') as stream:
            print >> stream, names
        self.estimators = learner.build_estimators(dataset, self.TARGET_COUNT)
    def distance(self, graph, source, destination):
        distance = 0
        for i in range(self.DIMENSION):
            distance += abs(graph.node[source]['position'][i] - graph.node[destination]['position'][i])
        return distance
    def center(self, graph, source, destination):
        center = [source, destination]
        for i in range(self.DIMENSION):
            center[i] = .5*(graph.node[source]['position'][i] + graph.node[destination]['position'][i])
        return center
    def generate_random_graph(self, degree):
        while True:
            graph = gnm_random_graph(self.NODE_COUNT, self.NODE_COUNT*degree)
            if is_connected(graph):
                for node_index, data in graph.nodes(data=True):
                    data['position'] = [node_index / self.RADIX, node_index % self.RADIX]
                for source, destination, data in graph.edges(data=True):
                    data['weight'] = self.distance(graph, source, destination)
                return graph
    def extract_features(self, graph):
        raw_features = [number_of_edges(graph), average_shortest_path_length(graph),
                    diameter(graph), radius(graph)]
        return raw_features
    def estimate_sample(self, raw_features):
        raw_sample = asarray(range(self.TARGET_COUNT) + raw_features)
        sample = actuator.scaler.transform(raw_sample)
        for i in range(self.TARGET_COUNT):
            sample[i] = (self.estimators[i].predict(sample[self.TARGET_COUNT:])).tolist()[0]
        return sample
    def evaluate_quality(self, raw_sample):
        return - raw_sample[0] * raw_sample[1]
    def build_dataset(self):
        for round in range(1000):
            graph = self.generate_random_graph(uniform(self.DEGREE_MIN, self.DEGREE_MAX))
            actuator.add_data(graph, self.TARGET_TOKENS, learner.DATASET)
performer = Performer()
graph = performer.generate_random_graph(2)


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
sensor = Sensor()
    
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
        with open(self.TOPOLOGY, 'w+') as stream:
            for node in graph:
                destinations = []
                for destination in graph[node]:
                    destinations += ['router', str(destination), str(graph[node][destination]['weight'])]
                destinations_string = ' '.join(map(str, destinations))
                print 'router', node, 'node', node, destinations_string
        with open(self.SIMULATION_LOG, 'w') as stream:
            check_call([self.SIMULATOR, self.CONFIGURATION], stdout = stream)
        raw_targets = sensor.extract_targets(self.SIMULATION_LOG, target_tokens)
        raw_features = performer.extract_features(graph)
        raw_sample = raw_targets + raw_features
        if dataset == performer.TRACE:
            raw_sample.insert(0, -performer.evaluate_quality(raw_sample))
        with open(dataset, 'a') as stream:
            print >> stream, '\t'.join(map(str, raw_sample))
actuator = Actuator()
# actuator.add_data(graph, performer.TARGET_TOKENS, learner.DATASET)
# from matplotlib.pyplot import show
# draw(graph, get_node_attributes(graph, 'position'), hold = True)
# draw_networkx_edge_labels(graph, get_node_attributes(graph, 'position'), alpha = 0.2)
# show()

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
        sample = performer.estimate_sample(raw_features)
        raw_sample = actuator.scaler.inverse_transform(asarray(sample))
        quality = performer.evaluate_quality(raw_sample)
        return quality
    def generate_random_state(self):
        state = performer.generate_random_graph(uniform(performer.DEGREE_MIN, performer.DEGREE_MAX))
        return state
optimization = Optimization()

# performer.build_dataset()
# performer.update_estimators(learner.DATASET)
# final = hill_climbing_random_restarts(optimization, 4, 1000)
