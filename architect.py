#!/usr/bin/env python
from multiprocessing import Pool
from shutil import copyfile
from ast import literal_eval
from os import devnull
from os import rename
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
from datetime import datetime
from subprocess import check_call
from simpleai.search import SearchProblem
from simpleai.search.local import hill_climbing
from simpleai.search.local import hill_climbing_random_restarts
from simpleai.search.local import beam
from simpleai.search.local import beam_best_first
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
from networkx import to_dict_of_dicts
from networkx import to_edgelist
from networkx import shortest_path
from networkx import shortest_path_length
from networkx import average_shortest_path_length
from numpy import loadtxt
from numpy import savetxt
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
from pandas import DataFrame
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
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
            print 'learner: build_estimators: benchmark =', performer.benchmark
            print 'best_params=', estimators[i].best_params_,
            print 'best_score=', estimators[i].best_score_
        return estimators
learner = Learner()

class Performer(object):
    optimization_targets = ['latency', 'power', 'power_latency_product']
    optimization_target = 'latency'
    benchmarks = ['bodytrack', 'canneal', 'dedup', 'fluidanimate', 'freqmine', 'swaption', 'vips']
    benchmark = None
    document_directory = 'documents/'
    tex = 'architect.tex'
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
        entry['design'] = 'design_' + benchmark + '.log'
        entry['trace'] = document_directory +'trace_' + benchmark + '.png'
        entry['links'] = document_directory +'links_' + benchmark + '.png'
        entry['result'] = document_directory +'result_' + benchmark + '.png'
        database[benchmark] = entry
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
    def set_radix(self, radix):
        self.RADIX = radix
    def set_benchmark(self, benchmark):
        self.benchmark = benchmark
        print 'performer: initialized', self.benchmark, self.optimization_target
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
    def get_edge_weight_histogram(self, graph):
        edge_weights=[]
        for edge in graph.edges(data = True):
            edge_weights.append(edge[2]['weight'] - self.NODE_WEIGHT)
        edge_weight_histogram = histogram(edge_weights, bins = max(edge_weights))[0].tolist()
        return edge_weight_histogram
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
        if self.optimization_target == 'power_latency_product':
            return -(raw_targets[0] * raw_targets[1])
        elif self.optimization_target == 'latency':
            return -raw_targets[0]
        elif self.optimization_target == 'power':
            return -raw_targets[1]
        else:
            raise NameError('unknown optimization_target')
    def string_to_graph(self, graph_string):
        return Graph(literal_eval(graph_string))
    def get_targets(self, graph):
        return [1,2]
        # return actuator.evaluate_metrics(self.benchmark, graph, self.TARGET_TOKENS)
    def get_path_length(self, graph):
        return self.weighted_length(performer.database[self.benchmark]['traffic'], graph, 'weight')
    def get_degree(self, graph):
        return graph.degree().values()
    def get_degree_norm(self, degrees):
        return norm(degrees)**2
    def review(self):
        final = read_csv(self.database[self.benchmark]['design'], index_col = 'time ',
                        sep = '\t', skipinitialspace = True)
        final['graph'] = map(self.string_to_graph, final['design'])
        final['edge_weight_distribution'] = map(self.get_edge_weight_histogram, final['graph'])
        final['edge_count'] = map(number_of_edges, final['graph'])
        final['path_length'] = map(self.get_path_length, final['graph'])
        final['diameter'] = map(diameter, final['graph'])
        final['radius'] = map(radius, final['graph'])
        final['real_latency'], final['real_power'] = zip(*map(self.get_targets, final['graph']))
        final['real_latency_power_product'] = map(mul, final['real_latency'], final['real_power'])
        final['degrees'] = map(self.get_degree, final['graph'])
        final['degree_average'] = map(average, final['degrees'])
        final['degree_max'] = map(max, final['degrees'])
        final['degree_min'] = map(min, final['degrees'])
        final['degree_norm'] = map(self.get_degree_norm, final['degrees'])
        print final[['degree_average', 'degree_max', 'degree_min', 'degree_norm']]
        return final
        # w1 = self.weighted_length(self.database[self.benchmark]['traffic'], graph, 'weight')
        # for source, destination, design in graph.edges(data=True):
        #     design['weight'] = self.NODE_WEIGHT
        # w2 = self.weighted_length(self.database[self.benchmark]['traffic'], graph, 'weight')
        # print w1/w2
        # pprint(to_dict_of_dicts(graph))
        # pprint(shortest_path_length(graph))
        # pprint(shortest_path_length(graph, weight = 'weight'))
        return
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
        return
    def evaluate_metrics(self, benchmark, graph, target_tokens):
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
        real_raw_targets = sensor.extract_targets(performer.database[benchmark]['simulation_log'], target_tokens)
        return real_raw_targets
    def add_data(self, benchmark, graph, target_tokens, dataset, initial = False):
        print 'actuator: add_data:', 'benchmark =', benchmark
        real_raw_targets = self.evaluate_metrics(benchmark, graph, target_tokens)
        raw_features = performer.extract_features(benchmark, graph)
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
        return
    def reformat(self, benchmark):
        final = read_csv(performer.database[benchmark]['design'], index_col = 'time ',
                        sep = '\t', skipinitialspace = True)
        print final
        # final.insert(0, 'benchmark', benchmark)
        # final.insert(1, 'optimization_target', 'power_latency_product')
        # final.to_csv(performer.database[benchmark]['design'], sep = '\t')
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
    savefig(temp.png)
    return

def visualize(benchmark, quantity):
    performer.set_benchmark(benchmark)
    data_file = None
    axes = None
    figure()
    if quantity == 'links':
        data = performer.review()
        best_design = data.ix[data['real_latency_power_product'].idxmin()]
        frequencies = best_design['edge_weight_distribution']
        lengths = [x+1 for x in range(len(frequencies))]
        data_frame = DataFrame(frequencies, index = lengths, columns = ['weight_frequency'])
        print data_frame
        axes = data_frame.loc[:,'weight_frequency'].plot(kind = 'bar')
        axes.set_xlabel(benchmark + '_network_link_weight')
        axes.set_ylabel('degree (frequency)')
    if quantity == 'result':
        data = performer.review()
        data_filtered = data[data['real_latency_power_product'] < 900]
        axes = data_filtered.loc[:,['real_latency_power_product']].plot(kind = 'hist')
        axes.set_xlabel(benchmark + '_network_latency_power_product')
    elif quantity == 'trace':
        data_file = 'dataset'
        data = read_csv(performer.database[benchmark][data_file], sep = '\t', skipinitialspace = True)
        axes = data.loc[100:,['real_latency_power_product']].plot()
        axes.set_xlabel(benchmark + '_network_optimization_step')
    axes.get_figure().savefig(performer.database[benchmark][quantity])
    return
def analyze(benchmark):
    performer.set_benchmark(benchmark)
    # for interest in ['trace', 'result', 'links']:
        # visualize(benchmark, interest)
    return

def design(benchmark):
    performer.set_benchmark(benchmark)
    restarts = 10
    iterations = 200
    performer.update_estimators(performer.database[performer.benchmark]['dataset'], 4)
    for trial in range(restarts):
        print 'design:', 'benchmark =', performer.benchmark + ';',
        print 'optimization_target =', performer.optimization_target + ';',
        print 'trial =', trial
        final = hill_climbing_random_restarts(optimization, 1, iterations)
        with open(performer.database[performer.benchmark]['design'], 'a') as stream:
            print >> stream, (performer.benchmark + '\t', performer.optimization_target + '\t',
                              str(datetime.now()) + '\t', to_dict_of_dicts(final.state))
    return

if __name__ == '__main__':
    pool = Pool(8)
    pool.map(design, performer.benchmarks)
    # for benchmark in performer.benchmarks:
        # analyze(benchmark)
        # actuator.reformat(benchmark)
