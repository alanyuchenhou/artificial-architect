#!/usr/bin/env python
from shutil import copyfile
from os import devnull
from pprint import pprint
from copy import copy
from cProfile import run
from fileinput import input
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
from simpleai.search.local import simulated_annealing
from networkx import Graph
from networkx import nodes
from networkx import get_node_attributes
from networkx import get_edge_attributes
from networkx import neighbors
from networkx import is_connected
from networkx import diameter
from networkx import number_of_edges
from networkx import radius
from networkx import degree
from networkx import degree_histogram
from networkx import density
from networkx import draw
from networkx import draw_networkx_edge_labels
from networkx import gnm_random_graph
from networkx import to_numpy_matrix
from networkx import to_dict_of_lists
from networkx import to_dict_of_dicts
from networkx import to_edgelist
from networkx import shortest_path_length
from networkx import average_shortest_path_length
from numpy import loadtxt
from numpy import savetxt
from numpy import genfromtxt
from numpy import delete
from numpy import arange
from numpy import asarray
from numpy import zeros
from numpy import average
from numpy import repeat
from numpy import dot
from numpy.linalg import norm
from numpy import fill_diagonal
from numpy import vstack
from numpy import hstack
from numpy import tile
from numpy import hsplit
from numpy import vsplit
from numpy import logspace
from numpy import linspace
from numpy import squeeze
from numpy import histogram
from sklearn import datasets
from sklearn.svm import SVR
from sklearn.svm import SVC
from sklearn.grid_search import GridSearchCV
from sklearn.preprocessing import scale
from sklearn.preprocessing import StandardScaler
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
from matplotlib.pyplot import plot
from matplotlib.pyplot import subplot
from matplotlib.pyplot import legend
from matplotlib.pyplot import axis
from matplotlib.pyplot import yscale
from matplotlib.pyplot import ylabel
from matplotlib.pyplot import xlabel
from matplotlib.pyplot import show
from matplotlib.pyplot import savefig
from matplotlib.pyplot import plotfile

class Critic(object):
    def evaluate_kernels(self, dataset):
        data = actuator.load_data(dataset, range(performer.SAMPLE_COUNT))
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
    def build_estimators(self, dataset, target_count, accuracy):
        data = actuator.load_data(dataset, range(performer.SAMPLE_SIZE))
        c_range = accuracy
        gamma_range = accuracy
        parameters = {'C' : logspace(0, c_range, c_range+1).tolist(),
                      'gamma' : logspace(- gamma_range, 0, gamma_range+1).tolist()}
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
    RADIX = 8
    NODE_COUNT = RADIX ** DIMENSION
    NODE_WEIGHT = 4
    EDGE_COUNT_MIN = 70
    EDGE_COUNT_MAX = 200
    TARGET_NAMES = ['latency', 'power']
    TARGET_TOKENS = ['Flit latency average = ', '- Total Power:             ']
    TARGET_COUNT = len(TARGET_NAMES)
    FEATURE_NAMES = ['edge_count', 'path_length', 'diameter', 'radius', 'degree_norm']
    FEATURE_COUNT = len(FEATURE_NAMES)
    SAMPLE_SIZE = TARGET_COUNT + FEATURE_COUNT
    BENCHMARKS = ['bodytrack', 'canneal', 'dedup', 'fluidanimate', 'freqmine', 'swaption', 'vips']
    benchmark = BENCHMARKS[0]
    print benchmark
    TRAFFIC = sum(loadtxt('traffic_' + benchmark + '.txt'))
    TRAFFIC /= (sum(TRAFFIC)*.001)
    print TRAFFIC
    DATASET = 'dataset.' + benchmark + '.dat'
    STATS = 'stats.' + benchmark + '.dat'
    DESIGN = 'design.' + benchmark + '.log'
    FIGURE = 'trace-' + benchmark + '.png'
    DOCUMENT = 'architect'
    estimators = []
    def update_traffic(self):
        node_string = 'traffic = hotspot({{' + ','.join(map(str, range(performer.NODE_COUNT))) + '},'
        traffic_string = '{'+ ','.join(map(str, self.TRAFFIC.tolist())) + '}});'
        for line in input(actuator.CONFIGURATION, inplace = True):
            if line.startswith('traffic ='):
                print line.replace(line, node_string + traffic_string)
            else:
                print line.replace(line, line),
    def extract_features(self, graph):
        raw_features = [number_of_edges(graph),
                        self.weighted_average_shortest_path_length(graph, 'weight'),
                        diameter(graph), radius(graph), norm(graph.degree().values())**2]
        return raw_features
    def initialize_data(self):
        HEADER = self.TARGET_NAMES
        names = 'real_' + '\t real_'.join(HEADER)
        names += '\t' + '\t'.join(self.FEATURE_NAMES)
        names += '\t real_latency_power_product \t predicted_latency_power_product'
        names += '\t predicted_' + '\t predicted_'.join(HEADER) + '\n'
        with open(performer.DATASET, 'w+') as stream:
            print >> stream, names
        with open(performer.STATS, 'w+') as stream:
            print >> stream, 'time \t', 'edge_weight_distribution \t', names
        with open(performer.DESIGN, 'w+') as stream:
            print >> stream, 'time \t' + 'design'
    def update_estimators(self, dataset, accuracy):
        self.estimators = learner.build_estimators(dataset, self.TARGET_COUNT, accuracy)
    def distance(self, graph, source, destination):
        distance = graph.node[source]['weight']
        for i in range(self.DIMENSION):
            distance += abs(graph.node[source]['position'][i] - graph.node[destination]['position'][i])
        return distance
    def center(self, graph, source, destination):
        center = [source, destination]
        for i in range(self.DIMENSION):
            center[i] = .5*(graph.node[source]['position'][i] + graph.node[destination]['position'][i])
        return center
    def generate_random_graph(self, edge_count):
        while True:
            graph = gnm_random_graph(self.NODE_COUNT, edge_count)
            if is_connected(graph):
                for node_index, data in graph.nodes(data=True):
                    data['position'] = [node_index / self.RADIX, node_index % self.RADIX]
                    data['weight'] = self.NODE_WEIGHT
                for source, destination, data in graph.edges(data=True):
                    data['weight'] = self.distance(graph, source, destination)
                return graph
    def weighted_average_shortest_path_length(self, graph, weight):
        raw_path_lengths = shortest_path_length(graph, weight = weight)
        path_lengths = zeros((self.NODE_COUNT, self.NODE_COUNT))
        for source in raw_path_lengths:
            for destination in raw_path_lengths[source]:
                path_lengths[source][destination] = raw_path_lengths[source][destination]
        averaged_traffic = tile(self.TRAFFIC, (self.NODE_COUNT,1))
        return average(path_lengths, weights = averaged_traffic)
    def estimate_sample(self, raw_features):
        raw_sample = asarray(range(self.TARGET_COUNT) + raw_features)
        predicted_sample = actuator.scaler.transform(raw_sample)
        for i in range(self.TARGET_COUNT):
            predicted_sample[i] = (self.estimators[i].predict(
                    predicted_sample[self.TARGET_COUNT:])).tolist()[0]
        predicted_raw_sample = actuator.scaler.inverse_transform(asarray(predicted_sample)).tolist()
        predicted_raw_targets = predicted_raw_sample[:self.TARGET_COUNT]
        return predicted_raw_targets
    def evaluate_quality(self, raw_targets):
        return -(raw_targets[0] * raw_targets[1])
    def build_dataset(self, instance_count):
        for round in range(instance_count):
            graph = self.generate_random_graph(uniform(70, 200))
            actuator.add_data(graph, self.TARGET_TOKENS, performer.DATASET, initial = True)
performer = Performer()

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
    def load_data(self, dataset, columns):
        raw_dataset = loadtxt(dataset, usecols = columns, skiprows = 1)
        self.scaler.fit(raw_dataset)
        scaled_dataset = self.scaler.transform(raw_dataset)
        split_dataset = map(squeeze, hsplit(scaled_dataset,[1,2]))
        return split_dataset
    def add_data(self, graph, target_tokens, dataset, initial = False):
        with open(self.TOPOLOGY, 'w+') as stream:
            for source in graph:
                destinations = []
                for destination in graph[source]:
                    destinations += ['router', str(destination),
                                     str(graph[source][destination]['weight'] - performer.NODE_WEIGHT)]
                destinations_string = ' '.join(map(str, destinations))
                print >> stream, 'router', source, 'node', source, destinations_string
        with open(self.SIMULATION_LOG, 'w+') as stream:
            with open('error.log', 'w+') as error_log:
                check_call([self.SIMULATOR, self.CONFIGURATION], stdout = stream, stderr = error_log)
        raw_features = performer.extract_features(graph)
        real_raw_targets = sensor.extract_targets(self.SIMULATION_LOG, target_tokens)
        real_raw_sample = real_raw_targets + raw_features
        real_quality = performer.evaluate_quality(real_raw_targets)
        data_instance = []
        predicted_raw_targets = real_raw_targets
        predicted_quality = real_quality
        if initial == False:
            predicted_raw_targets = performer.estimate_sample(raw_features)
            predicted_quality = performer.evaluate_quality(predicted_raw_targets)
        data_instance = (real_raw_sample + [- real_quality] +
                         [- predicted_quality] + predicted_raw_targets)
        print(data_instance)
        with open(dataset, 'a') as stream:
            print >> stream, '\t'.join(map(str, data_instance))
actuator = Actuator()
# actuator.add_data(graph, performer.TARGET_TOKENS, performer.DATASET)

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
        actuator.add_data(state, performer.TARGET_TOKENS, performer.DATASET)
        successors = []
        for cluster in combinations(nodes(state),2):
            successor = state.copy()
            for node_pair in combinations(cluster,2):
                if node_pair[0] in successor.neighbors(node_pair[1]):
                    successor.remove_edge(node_pair[0],node_pair[1])
                else:
                    successor.add_edge(node_pair[0], node_pair[1],
                                       weight = performer.distance(state, node_pair[0], node_pair[1]))
            if is_connected(successor):
                successors.append(successor)
        return successors
    def result(self, state, action):
        return action
    def value(self, state):
        raw_features = performer.extract_features(state)
        predicted_raw_targets = performer.estimate_sample(raw_features)
        predicted_quality = performer.evaluate_quality(predicted_raw_targets)
        return predicted_quality
    def generate_random_state(self):
        performer.update_estimators(performer.DATASET, 4)
        state = performer.generate_random_graph(uniform(80, 100))
        return state
optimization = Optimization()

def run():
    performer.initialize_data()
    performer.update_traffic()
    performer.build_dataset(100)
    for i in range(10):
        result = hill_climbing_random_restarts(optimization, 1)
        time_stamp = strftime('%Y-%m-%d-%H-%m-%S') + '\t'
        with open(performer.DESIGN, 'a') as stream:
            print >> stream, time_stamp, to_dict_of_dicts(result.state)
        edge_weights=[]
        for edge in result.state.edges(data = True):
            edge_weights.append(edge[2]['weight'] - performer.NODE_WEIGHT)
        edge_weight_histogram = histogram(edge_weights, bins = max(edge_weights))[0].tolist()
        with open(performer.STATS, 'a') as stream:
            print >> stream, time_stamp, edge_weight_histogram, '\t',
        actuator.add_data(result.state, performer.TARGET_TOKENS, performer.STATS)
def analyze():
    raw_data = genfromtxt(performer.DATASET, names = True)
    data = delete(raw_data, range(100))
    figure(figsize = (14, 10))
    for column in data.dtype.names:
        if (column == 'predicted_latency_power_product' or column == 'real_latency_power_product'):
            subplot(411)
        elif (column == 'real_latency' or column == 'predicted_latency'):
            subplot(412)
        elif (column == 'real_power' or column == 'predicted_power'):
            subplot(413)
        else:
            subplot(414)
            yscale('log')
            xlabel('step')
        plot(data[column], label = column)
        legend(loc = 'upper right').get_frame().set_alpha(.1)
    savefig(performer.FIGURE)
    check_call(['pdflatex', performer.DOCUMENT])

# graph = performer.generate_random_graph(99)
# from matplotlib.pyplot import show
# draw(graph, get_node_attributes(graph, 'position'), hold = True)
# draw_networkx_edge_labels(graph, get_node_attributes(graph, 'position'), alpha = 0.2)
# show()

# run()
analyze()
