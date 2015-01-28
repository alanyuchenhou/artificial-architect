#!/usr/bin/env python
from multiprocessing import Pool
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
from time import strftime
from subprocess import check_call
from simpleai.search import SearchProblem
from simpleai.search.local import hill_climbing_random_restarts
from simpleai.search.local import simulated_annealing
from sklearn import datasets
from sklearn.svm import SVR
from sklearn.svm import SVC
from sklearn.grid_search import GridSearchCV
from sklearn.preprocessing import scale
from sklearn.preprocessing import StandardScaler
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
from pandas import read_csv
from matplotlib import use
use('Agg')
from matplotlib.pyplot import savefig

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
    benchmarks = ['bodytrack', 'canneal', 'dedup', 'fluidanimate', 'freqmine', 'swaption', 'vips']
    configuration_mesh_template = 'booksim2/src/examples/mesh88_lat'
    simulation_log_mesh = 'simulation_mesh.log'
    database = {}
    for benchmark in benchmarks:
        entry = {}
        traffic = sum(loadtxt('traffic_' + benchmark + '.txt'))
        traffic /= (sum(traffic)*.001)
        entry['traffic'] = traffic
        entry['topology'] = 'booksim2/src/examples/anynet/anynet_file_' + benchmark
        entry['configuration'] = 'booksim2/src/examples/anynet/anynet_config_' + benchmark
        entry['configuration_mesh'] = 'booksim2/src/examples/mesh88_lat_' + benchmark
        entry['simulation_log'] = 'simulation_' + benchmark +'.log'
        entry['dataset'] = 'dataset_' + benchmark + '.dat'
        entry['stats'] = 'stats_' + benchmark + '.dat'
        entry['design'] = 'design_' + benchmark + '.log'
        entry['trace'] = 'zulu/trace_' + benchmark + '.png'
        entry['result'] = 'zulu/result_' + benchmark + '.png'
        database[benchmark] = entry
    # pprint(database)
    benchmark = benchmarks[0]
    DOCUMENT = 'architect'
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
    estimators = []
    def extract_features(self, benchmark, graph):
        raw_features = [number_of_edges(graph),
                        self.weighted_length(performer.database[benchmark]['traffic'], graph, 'weight'),
                        diameter(graph), radius(graph), norm(graph.degree().values())**2]
        return raw_features
    def set_benchmark(self, benchmark):
        self.benchmark = benchmark
        print 'benchmark =', self.benchmark
    def initialize_mesh(self, benchmark):
        self.benchmark = benchmark
        print 'benchmark =', self.benchmark
        node_string = 'hotspot({{' + ','.join(map(str, range(performer.NODE_COUNT))) + '},'
        traffic_string = '{'+ ','.join(map(str, self.database[benchmark]['traffic'].tolist())) + '}})'
        copyfile(self.configuration_mesh_template, self.database[benchmark]['configuration_mesh'])
        for line in input(self.database[benchmark]['configuration_mesh'], inplace = True):
            if line.startswith('traffic ='):
                print line.replace(line, 'traffic = ' + node_string + traffic_string + ';')
            elif line.startswith('injection_rate ='):
                print line.replace(line, line),
            else:
                print line.replace(line, line),
    def initialize(self, benchmark, instance_count):
        self.set_benchmark(benchmark)
        node_string = 'hotspot({{' + ','.join(map(str, range(performer.NODE_COUNT))) + '},'
        traffic_string = '{'+ ','.join(map(str, self.database[benchmark]['traffic'].tolist())) + '}})'
        for line in input(self.database[benchmark]['configuration'], inplace = True):
            if line.startswith('network_file ='):
                print line.replace(line, 'network_file = ' + self.database[benchmark]['topology'] + ';')
            elif line.startswith('traffic ='):
                print line.replace(line, 'traffic = ' + node_string + traffic_string + ';')
            elif line.startswith('injection_rate ='):
                print line.replace(line, line),
            else:
                print line.replace(line, line),
        HEADER = self.TARGET_NAMES
        names = 'real_' + '\t real_'.join(HEADER)
        names += '\t' + '\t'.join(self.FEATURE_NAMES)
        names += '\t real_latency_power_product\t predicted_latency_power_product'
        names += '\t predicted_' + '\t predicted_'.join(HEADER)
        with open(performer.database[benchmark]['dataset'], 'w+') as stream:
            print >> stream, names
        with open(performer.database[benchmark]['stats'], 'w+') as stream:
            print >> stream, 'time\t', 'edge_weight_distribution\t', names
        with open(performer.database[benchmark]['design'], 'w+') as stream:
            print >> stream, 'time\t' + 'design'
        for round in range(instance_count):
            graph = self.generate_random_graph(uniform(70, 200))
            actuator.add_data(benchmark, graph, self.TARGET_TOKENS,
                              performer.database[benchmark]['dataset'], initial = True)
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
    def weighted_length(self, traffic, graph, weight):
        raw_path_lengths = shortest_path_length(graph, weight = weight)
        path_lengths = zeros((self.NODE_COUNT, self.NODE_COUNT))
        for source in raw_path_lengths:
            for destination in raw_path_lengths[source]:
                path_lengths[source][destination] = raw_path_lengths[source][destination]
        averaged_traffic = tile(traffic, (self.NODE_COUNT,1))
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
    SIMULATOR = 'booksim2/src/booksim'
    scaler = StandardScaler()
    def load_data(self, dataset, columns):
        raw_dataset = loadtxt(dataset, usecols = columns, skiprows = 1)
        self.scaler.fit(raw_dataset)
        scaled_dataset = self.scaler.transform(raw_dataset)
        split_dataset = map(squeeze, hsplit(scaled_dataset,[1,2]))
        return split_dataset
    def add_data_mesh(self, benchmark, target_tokens, initial = False):
        with open(performer.simulation_log_mesh, 'w+') as stream:
            with open('error.log', 'w+') as error_log:
                check_call([self.SIMULATOR, performer.database[benchmark]['configuration_mesh']],
                           stdout = stream, stderr = error_log)
        real_raw_targets = sensor.extract_targets(
            performer.simulation_log_mesh, target_tokens)
        real_quality = performer.evaluate_quality(real_raw_targets)
        data_instance = []
        data_instance = (real_raw_targets + [- real_quality])
        print '\t'.join(map(str, data_instance))
    def add_data(self, benchmark, graph, target_tokens, dataset, initial = False):
        with open(performer.database[benchmark]['topology'], 'w+') as stream:
            for source in graph:
                destinations = []
                for destination in graph[source]:
                    destinations += ['router', str(destination),
                                     str(graph[source][destination]['weight'] - performer.NODE_WEIGHT)]
                destinations_string = ' '.join(map(str, destinations))
                print >> stream, 'router', source, 'node', source, destinations_string
        with open(performer.database[benchmark]['simulation_log'], 'w+') as stream:
            with open('error.log', 'w+') as error_log:
                check_call([self.SIMULATOR, performer.database[benchmark]['configuration']],
                           stdout = stream, stderr = error_log)
        raw_features = performer.extract_features(benchmark, graph)
        real_raw_targets = sensor.extract_targets(
            performer.database[benchmark]['simulation_log'], target_tokens)
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
        with open(dataset, 'a') as stream:
            print >> stream, '\t'.join(map(str, data_instance))
actuator = Actuator()

class Optimization(SearchProblem):
    def actions(self, state):
        actuator.add_data(performer.benchmark, state, performer.TARGET_TOKENS,
                          performer.database[performer.benchmark]['dataset'])
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
        raw_features = performer.extract_features(performer.benchmark, state)
        predicted_raw_targets = performer.estimate_sample(raw_features)
        predicted_quality = performer.evaluate_quality(predicted_raw_targets)
        return predicted_quality
    def generate_random_state(self):
        state = performer.generate_random_graph(uniform(80, 100))
        return state
optimization = Optimization()

def draw_graph(graph):
    draw(graph, get_node_attributes(graph, 'position'), hold = True)
    draw_networkx_edge_labels(graph, get_node_attributes(graph, 'position'), alpha = 0.2)
    show()
    return

def design(benchmark):
    restarts = 10
    iterations = 200
    for trial in range(restarts):
        print 'benchmark =', benchmark, 'trial =', trial, '/', restarts
        performer.update_estimators(performer.database[benchmark]['dataset'], 4)
        final = hill_climbing_random_restarts(optimization, 1, iterations)
        time_stamp = strftime('%Y-%m-%d-%H-%m-%S') + '\t'
        with open(performer.database[benchmark]['design'], 'a') as stream:
            print >> stream, time_stamp, to_dict_of_dicts(final.state)
        edge_weights=[]
        for edge in final.state.edges(data = True):
            edge_weights.append(edge[2]['weight'] - performer.NODE_WEIGHT)
        edge_weight_histogram = histogram(edge_weights, bins = max(edge_weights))[0].tolist()
        with open(performer.database[benchmark]['stats'], 'a') as stream:
            print >> stream, time_stamp, edge_weight_histogram, '\t',
        actuator.add_data(benchmark, final.state, performer.TARGET_TOKENS, performer.database[benchmark]['stats'])
    return

def analyze(benchmark):
    data = read_csv(performer.database[benchmark]['stats'], sep = '\t', skipinitialspace = True)
    # axes = data.loc[:,['real_latency_power_product ']].plot(kind = 'hist', alpha = .5)
    # axes.set_xlabel('latency_power_product')
    # axes.get_figure().savefig(performer.database[benchmark]['result'])

    data = read_csv(performer.database[benchmark]['dataset'], sep = '\t', skipinitialspace = True)
    axes = data.loc[100:,['real_latency_power_product ', 'predicted_latency_power_product']].plot(alpha = .5)
    axes.set_xlabel('step')
    axes.get_figure().savefig(performer.database[benchmark]['trace'])
    return

if __name__ == '__main__':
    for benchmark in performer.benchmarks:
        # performer.initialize(benchmark, 100)
        performer.set_benchmark(benchmark)
    # pool = Pool(8)
    # pool.map(design, performer.benchmarks)
    for benchmark in performer.benchmarks:
        analyze(benchmark)
    check_call(['pdflatex', performer.DOCUMENT])
