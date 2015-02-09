#!/usr/bin/env python
# total power is used! need to use wire power
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
from simpleai.search.local import hill_climbing_stochastic
from simpleai.search.local import hill_climbing_random_restarts
from simpleai.search.local import beam
from simpleai.search.local import beam_best_first
from simpleai.search.local import simulated_annealing
from sklearn.svm import SVR
from sklearn.svm import SVC
from sklearn.grid_search import GridSearchCV
from sklearn.preprocessing import scale
from sklearn.preprocessing import StandardScaler
from networkx import Graph
from networkx import relabel_nodes
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
from networkx import grid_2d_graph
from networkx import connected_watts_strogatz_graph
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
from numpy import prod
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
from numpy.linalg import norm
from numpy.random import rand
from pandas import read_csv
from pandas import DataFrame
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
from matplotlib.pyplot import title
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
        return

class Performer(object):
    optimization_targets = ['latency', 'power', 'latency_power_product']
    optimization_target = optimization_targets[1]
    benchmarks = ['bodytrack', 'canneal', 'dedup', 'fluidanimate', 'freqmine', 'swaption', 'vips']
    benchmark = None
    document_directory = 'documents/'
    tex = 'architect.tex'
    stats = {'mesh': 'stats_mesh.tsv',
             'freenet': 'stats_freenet.tsv',
             'accuracy': 'estimation_accuracy.tsv'}
    configuration_template = {'mesh': 'booksim2/src/examples/mesh88_lat',
                              'freenet': 'booksim2/src/examples/anynet/anynet_config'}
    image = {'latency': document_directory + 'latency',
             'degree': document_directory + 'degree',
             'average_hop_count': document_directory + 'average_hop_count',
             'average_path_length': document_directory + 'average_path_length'}
    database = {}
    for benchmark in benchmarks:
        entry = {}
        traffic = sum(loadtxt('traffic_' + benchmark + '.txt'))
        injection_rate = sum(traffic)
        traffic /= (injection_rate*.0001)
        entry['traffic'] = traffic
        entry['topology'] = 'booksim2/src/examples/anynet/anynet_file_' + benchmark
        entry['configuration_freenet'] = 'booksim2/src/examples/anynet/anynet_config_' + benchmark
        entry['configuration_mesh'] = 'booksim2/src/examples/mesh88_lat_' + benchmark
        entry['simulation_log_freenet'] = 'simulation_anynet_' + benchmark +'.log'
        entry['simulation_log_mesh'] = 'simulation_mesh_' + benchmark +'.log'
        entry['dataset'] = 'dataset_' + benchmark + '.tsv'
        entry['design'] = 'design_' + benchmark + '.tsv'
        entry['design_mesh'] = 'design_mesh_' + benchmark + '.tsv'
        entry['stats_freenet'] = 'stats_' + benchmark + '.tsv'
        entry['stats_mesh'] = 'stats_mesh_' + benchmark + '.tsv'
        entry['trace'] = document_directory +'trace_' + benchmark + '.png'
        entry['links'] = document_directory +'links_' + benchmark + '.png'
        entry['result'] = document_directory +'result_' + benchmark + '.png'
        entry['network_figure'] = document_directory +'network_' + benchmark + '.png'
        database[benchmark] = entry
    injection_rate = 0.000001
    packet_size = 32
    DIMENSION = 2
    RADIX = 8
    NODE_WEIGHT = 4
    DEGREE_AVERAGE = 4
    DEGREE_MAX = 7
    NODE_COUNT = RADIX ** DIMENSION
    EDGE_COUNT_MIN = NODE_COUNT * DEGREE_AVERAGE / 3
    EDGE_COUNT_MAX = NODE_COUNT * DEGREE_AVERAGE / 2
    INITIAL_DATASET_SIZE = 100
    TARGET_NAMES = ['latency', 'power']
    # TARGET_TOKENS = ['Flit latency average = ', '- Channel Wire Power:      ']
    TARGET_TOKENS = ['Packet latency average = ', '- Total Power:             ']
    # TARGET_TOKENS = ['Packet latency average = ',  '- Channel Wire Power:      ']
    TARGET_COUNT = len(TARGET_NAMES)
    FEATURE_NAMES = ['edge_count', 'path_length', 'diameter', 'radius', 'degree_norm']
    FEATURE_COUNT = len(FEATURE_NAMES)
    SAMPLE_SIZE = TARGET_COUNT + FEATURE_COUNT
    estimators = []
    scaler = StandardScaler()
    def extract_features(self, benchmark, graph):
        raw_features = [number_of_edges(graph),
                        self.weighted_length(performer.database[benchmark]['traffic'], graph, 'weight'),
                        diameter(graph), radius(graph), norm(graph.degree().values())**2]
        return raw_features
    def set_radix(self, radix):
        self.RADIX = radix
        self.NODE_COUNT = self.RADIX ** self.DIMENSION
        self.EDGE_COUNT_MIN = self.NODE_COUNT * self.DEGREE_AVERAGE / 3
        self.EDGE_COUNT_MAX = self.NODE_COUNT * self.DEGREE_AVERAGE / 2
    def self_initialize(self, benchmark):
        if (benchmark not in self.benchmarks):
            raise NameError('unknown benchmark: ' + benchmark)
        self.benchmark = benchmark
        print 'performer: initialized:', 'benchmark = ' + self.benchmark + ';',
        print 'optimization_target = '+ self.optimization_target + ';'
        return
    def update_estimators(self, dataset, accuracy):
        data = self.load_data(dataset, range(performer.SAMPLE_SIZE))
        c_range = accuracy
        gamma_range = accuracy
        parameters = {'C' : logspace(0, c_range, c_range+1).tolist(),
                      'gamma' : logspace(- gamma_range, 0, gamma_range+1).tolist()}
        estimators = []
        svrs = []
        for i in range(self.TARGET_COUNT):
            svrs.append(SVR('rbf'))
            estimators.append(GridSearchCV(svrs[i], parameters, n_jobs = -1))
            estimators[i].fit(data[self.TARGET_COUNT], data[i])
            # print 'performer: update_estimator[' + str(i) + ']: benchmark =', performer.benchmark+';'
            # print 'performer: update_estimator[' + str(i) + ']: best_params =', estimators[i].best_params_, ';',
            # print 'best_score =', estimators[i].best_score_, ';'
        data_instance = [datetime.now(), self.benchmark, estimators[0].best_score_, estimators[1].best_score_]
        print  'performer: update_estimator: benchmark =', performer.benchmark+';', data_instance
        with open(self.stats['accuracy'], 'a') as f:
            f.write('\t'.join(map(str, data_instance)) + '\n')
        self.estimators = estimators
        return
    def link_length(self, graph, source, destination):
        manhattan_distance = 0
        for i in range(self.DIMENSION):
            manhattan_distance += abs(graph.node[source]['position'][i] - graph.node[destination]['position'][i])
        return manhattan_distance
    def edge_weight(self, graph, source, destination):
        weight = graph.node[source]['weight'] + self.link_length(graph, source, destination)
        return weight
    def center(self, graph, source, destination):
        center = [source, destination]
        for i in range(self.DIMENSION):
            center[i] = .5*(graph.node[source]['position'][i] + graph.node[destination]['position'][i])
        return center
    def constraints_satisfied(self, graph):
        degrees = self.get_degrees(graph)
        degree_average = average(degrees)
        degree_max = max(degrees)
        if degree_average <= self.DEGREE_AVERAGE and degree_max <= self.DEGREE_MAX and is_connected(graph):
            return True
        else:
            return False
    def process_graph(self, graph):
        for node_key, data in graph.nodes(data=True):
            data['position'] = (node_key / self.RADIX, node_key % self.RADIX)
            data['weight'] = self.NODE_WEIGHT
        for source, destination, data in graph.edges(data=True):
            data['length'] = self.link_length(graph, source, destination)
            data['weight'] = self.edge_weight(graph, source, destination)
        return
    def generate_random_graph(self):
        edge_count = uniform(self.EDGE_COUNT_MIN, self.EDGE_COUNT_MAX)
        while True:
            graph = gnm_random_graph(self.NODE_COUNT, edge_count)
            if self.constraints_satisfied(graph):
                self.process_graph(graph)
                return graph
    def key_mapping(self, tuple_key):
        new_key = tuple_key[0] * self.RADIX + tuple_key[1]
        return new_key
    def generate_grid_graph(self):
        tuple_keyed_graph = grid_2d_graph(self.RADIX, self.RADIX)
        graph = relabel_nodes(tuple_keyed_graph, self.key_mapping)
        self.process_graph(graph)
        return graph
    def generate_initial_graph(self):
        graph = connected_watts_strogatz_graph(self.NODE_COUNT, self.DEGREE_AVERAGE, uniform(0.1, 0.9))
        self.process_graph(graph)
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
    def load_data(self, dataset, columns):
        raw_dataset = loadtxt(dataset, usecols = columns, skiprows = 1)
        self.scaler.fit(raw_dataset)
        scaled_dataset = self.scaler.transform(raw_dataset)
        split_dataset = map(squeeze, hsplit(scaled_dataset,[1,2]))
        return split_dataset
    def estimate_metrics(self, raw_features):
        raw_sample = asarray(range(self.TARGET_COUNT) + raw_features)
        predicted_sample = self.scaler.transform(raw_sample)
        for i in range(self.TARGET_COUNT):
            predicted_sample[i] = (self.estimators[i].predict(predicted_sample[self.TARGET_COUNT:])).tolist()[0]
        predicted_raw_sample = self.scaler.inverse_transform(asarray(predicted_sample)).tolist()
        predicted_raw_targets = predicted_raw_sample[:self.TARGET_COUNT]
        return predicted_raw_targets
    def evaluate_quality(self, raw_targets):
        if self.optimization_target == 'latency_power_product':
            return -(raw_targets[0] * raw_targets[1])
        elif self.optimization_target == 'latency':
            return -raw_targets[0]
        elif self.optimization_target == 'power':
            return -raw_targets[1]
        else:
            raise NameError('unknown optimization_target')
    def add_data(self, dataset, initial, graph):
        real_raw_targets = actuator.evaluate_metrics('freenet', self.benchmark, graph)
        real_latency_power_product = prod(real_raw_targets)
        raw_features = self.extract_features(self.benchmark, graph)
        predicted_raw_targets = real_raw_targets
        if initial == False:
            predicted_raw_targets = self.estimate_metrics(raw_features)
        predicted_latency_power_product = prod(predicted_raw_targets)
        data_instance = real_raw_targets + raw_features + predicted_raw_targets
        data_instance += [real_latency_power_product, predicted_latency_power_product]
        print 'performer: add_data:', 'benchmark =', self.benchmark + ';', data_instance
        with open(dataset, 'a') as f:
            f.write('\t'.join(map(str, data_instance)) + '\n')
        return
    def initialize_dataset(self):
        for round in range(self.INITIAL_DATASET_SIZE):
            print 'performer: initialize_dataset: round =', round
            graph = self.generate_random_graph()
            self.add_data(self.database[self.benchmark]['dataset'], True, graph)
        return
    def generate_design_mesh(self):
        print 'performer: generate_design_mesh: benchmark =', self.benchmark
        graph = self.generate_grid_graph()
        design_instance = [datetime.now(), self.benchmark, self.optimization_target, to_dict_of_dicts(graph)]
        with open(self.database[self.benchmark]['design_mesh'], 'a') as f:
            f.write('\t'.join(map(str, design_instance)) + '\n')
        return
    def string_to_graph(self, graph_string):
        return Graph(literal_eval(graph_string))
    def get_network_figure(self, benchmark):
        return self.database[benchmark]['network_figure']
    def get_targets(self, graph):
        return actuator.evaluate_metrics('freenet', self.benchmark, graph)
    def get_mesh_metrics(self, benchmark):
        return actuator.evaluate_metrics('mesh', benchmark)
    def get_path_length(self, graph):
        return self.weighted_length(performer.database[self.benchmark]['traffic'], graph, 'weight')
    def get_degrees(self, graph):
        return graph.degree().values()
    def get_degrees_norm(self, degrees):
        return norm(degrees)**2
    def analyze_designs(self, architecture):
        print 'performer: analyze_designs: architecture = ' + architecture + '; benchmark = ' + self.benchmark + ';'
        design_file = None
        stats_file = None
        if architecture == 'freenet':
            design_file = 'design'
            stats_file = 'stats_freenet'
        elif architecture == 'mesh':
            design_file = 'design_mesh'
            stats_file = 'stats_mesh'
        final = read_csv(self.database[self.benchmark][design_file], sep = '\t', skipinitialspace = True)
        final['graph'] = map(self.string_to_graph, final['topology'])
        final['edge_weight_distribution'] = map(self.get_edge_weight_histogram, final['graph'])
        final['edge_count'] = map(number_of_edges, final['graph'])
        final['path_length'] = map(self.get_path_length, final['graph'])
        final['diameter'] = map(diameter, final['graph'])
        final['radius'] = map(radius, final['graph'])
        final['real_latency'], final['real_power'] = zip(*map(self.get_targets, final['graph']))
        final['real_latency_power_product'] = map(mul, final['real_latency'], final['real_power'])
        final['degrees'] = map(self.get_degrees, final['graph'])
        final['degree_average'] = map(average, final['degrees'])
        final['degree_max'] = map(max, final['degrees'])
        final['degree_min'] = map(min, final['degrees'])
        final['degree_norm'] = map(self.get_degrees_norm, final['degrees'])
        print final[['benchmark','real_latency', 'real_power', 'real_latency_power_product']]
        final.to_csv(performer.database[self.benchmark][stats_file], sep = '\t', index = False)
        # w1 = self.weighted_length(self.database[self.benchmark]['traffic'], graph, 'weight')
        # for source, destination, design in graph.edges(data=True):
        #     design['weight'] = self.NODE_WEIGHT
        # w2 = self.weighted_length(self.database[self.benchmark]['traffic'], graph, 'weight')
        # print w1/w2
        # pprint(to_dict_of_dicts(graph))
        # pprint(shortest_path_length(graph))
        # pprint(shortest_path_length(graph, weight = 'weight'))
        return
    # def evaluate_mesh(self):
    #     metrics = DataFrame({'benchmark': self.benchmarks})
    #     print metrics
    #     metrics['real_latency'], metrics['real_power'] = zip(*map(self.get_mesh_metrics, metrics['benchmark']))
    #     metrics['real_latency_power_product'] = metrics['real_latency'] * metrics['real_power']
    #     print metrics
    #     metrics.to_csv(self.stats['mesh'], sep = '\t', index = False)
    #     return
performer = Performer()

class Sensor(object):
    def extract_targets(self, simulation_log, target_tokens):
        with open(simulation_log, 'r') as f:
            target_values = copy(target_tokens)
            for line in f:
                for index in range(len(target_tokens)):
                    if line.startswith(target_tokens[index]):
                        value_string = (line.replace(target_tokens[index], '').partition(' ')[0])
                        target_values[index] = float(value_string)
        return target_values
sensor = Sensor()
    
class Actuator(object):
    SIMULATOR = 'booksim2/src/booksim'
    def configure_topology(self, benchmark, graph):
        with open(performer.database[benchmark]['topology'], 'w+') as f:
            for source in graph:
                connection = ['router', source, 'node', source]
                for destination in graph[source]:
                    connection += ['router', destination, graph[source][destination]['weight']-performer.NODE_WEIGHT]
                f.write(' '.join(map(str, connection)) + '\n')
        return
    def evaluate_metrics(self, architecture, benchmark, graph = None):
        if architecture == 'freenet':
            self.configure_topology(benchmark, graph)
        simulation_log = 'simulation_log_' + architecture
        configuration = 'configuration_' + architecture
        with open(performer.database[benchmark][simulation_log], 'w+') as f:
            with open('error.log', 'w+') as error_log:
                check_call([self.SIMULATOR, performer.database[benchmark][configuration]],
                           stdout = f, stderr = error_log)
        real_raw_targets = sensor.extract_targets(performer.database[benchmark][simulation_log],
                                                  performer.TARGET_TOKENS)
        return real_raw_targets
    def initialize_dataset_file(self, benchmark):
        columns = (['real_' + s for s in performer.TARGET_NAMES] + performer.FEATURE_NAMES
                           + ['predicted_' + s for s in performer.TARGET_NAMES]
                           + ['real_latency_power_product', 'predicted_latency_power_product'])
        with open(performer.database[benchmark]['dataset'], 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        return
    def initialize_freenet_design(self, benchmark):
        columns = ['time', 'benchmark', 'optimization_target', 'topology']
        with open(performer.database[benchmark]['design'], 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        return
    def initialize_mesh_design(self, benchmark):
        columns = ['time', 'benchmark', 'optimization_target', 'topology']
        with open(performer.database[benchmark]['design_mesh'], 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        return
    def initialize_accuracy_file(self, benchmark):
        columns = [datetime.now(), benchmark, 'latency_accuracy', 'power_accuracy']
        with open(performer.stats['accuracy'], 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        return
    # def reformat(self, benchmark):
    #     final = read_csv(performer.database[benchmark]['design'], sep = '\t', skipinitialspace = True)
    #     print final
    #     final.insert(0, 'benchmark', benchmark)
    #     final.insert(1, 'optimization_target', 'latency_power_product')
    #     final.to_csv(performer.database[benchmark]['design'], sep = '\t', index = False)
    #     return
    def initialize_configuration_file(self, benchmark, architecture):
        node_string = 'hotspot({{' + ','.join(map(str, range(performer.NODE_COUNT))) + '},'
        traffic_string = '{'+ ','.join(map(str, performer.database[benchmark]['traffic'].tolist())) + '}})'
        configuration = 'configuration_' + architecture
        copyfile(performer.configuration_template[architecture], performer.database[benchmark][configuration])
        for line in input(performer.database[benchmark][configuration], inplace = True):
            if line.startswith('network_file ='):
                print line.replace(line, 'network_file = ' + performer.database[benchmark]['topology'] + ';')
            elif line.startswith('traffic ='):
                print line.replace(line, 'traffic = ' + node_string + traffic_string + ';')
            elif line.startswith('packet_size ='):
                print line.replace(line, 'packet_size = ' + str(performer.packet_size) + ';')
            elif line.startswith('injection_rate ='):
                print line.replace(line, 'injection_rate = ' + str(performer.injection_rate) + ';')
            elif line.startswith('routing_delay  = '):
                print line.replace(line, 'routing_delay  = ' + str(performer.NODE_WEIGHT) + ';')
            else:
                print line.replace(line, line),
        return
    def initialize_files(self):
        self.initialize_accuracy_file(performer.benchmark)
        self.initialize_mesh_design(performer.benchmark)
        self.initialize_freenet_design(performer.benchmark)
        self.initialize_dataset_file(performer.benchmark)
        for architecture in performer.configuration_template:
            self.initialize_configuration_file(performer.benchmark, architecture)
        return
    def draw_graph(self, benchmark, graph_string, network_figure):
        figure()
        title(benchmark)
        graph = performer.string_to_graph(graph_string)
        performer.process_graph(graph)
        draw(graph, get_node_attributes(graph, 'position'), hold = True)
        # draw_networkx_edge_labels(graph, get_node_attributes(graph, 'position'), alpha = 0.2)
        savefig(network_figure)
        return
    def visualize(self, benchmark, quantity):
        data_file = 'dataset' if quantity == 'trace' else 'stats_freenet'
        axes = None
        figure()
        data = read_csv(performer.database[benchmark][data_file], sep = '\t', skipinitialspace = True)
        print data.columns.values
        if quantity == 'trace':
            print 'quantity = ', quantity
            # axes = data.loc[500:,['real_latency_power_product', 'predicted_latency_power_product']].plot()
            # axes = data.loc[100:,['real_latency', 'predicted_latency']].plot()
            axes = data.loc[500:,['real_power', 'predicted_power']].plot()
            axes.set_xlabel(benchmark + '_network_optimization_step')
        elif quantity == 'links':
            best_design = data.ix[data['real_latency_power_product'].idxmin()]
            frequencies = best_design['edge_weight_distribution']
            lengths = [x+1 for x in range(len(frequencies))]
            data_frame = DataFrame(frequencies, index = lengths, columns = ['weight_frequency'])
            print data_frame
            axes = data_frame.loc[:,'weight_frequency'].plot(kind = 'bar')
            axes.set_xlabel(benchmark + '_network_link_weight')
            axes.set_ylabel('degree (frequency)')
        elif quantity == 'result':
            print data[['benchmark', 'optimization_target', 'degree_average', 'degree_min', 'degree_max']]
            data_filtered = data[data['real_latency_power_product'] < 900]
            axes = data_filtered.loc[:,['real_latency_power_product']].plot(kind = 'hist')
            axes.set_xlabel(benchmark + '_network_latency_power_product')
        elif quantity == 'connectivity':
            pass
        axes.get_figure().savefig(performer.database[benchmark][quantity])
        return
actuator = Actuator()

class Optimization(SearchProblem):
    def actions(self, state):
        performer.add_data(performer.database[performer.benchmark]['dataset'], False, state)
        successors = []
        for cluster in combinations(nodes(state),2):
            successor = state.copy()
            for node_pair in combinations(cluster,2):
                if node_pair[0] in successor.neighbors(node_pair[1]):
                    successor.remove_edge(node_pair[0],node_pair[1])
                else:
                    successor.add_edge(node_pair[0], node_pair[1],
                                       weight = performer.edge_weight(state, node_pair[0], node_pair[1]))
            if performer.constraints_satisfied(successor):
                successors.append(successor)
        return successors
    def result(self, state, action):
        return action
    def value(self, state):
        raw_features = performer.extract_features(performer.benchmark, state)
        predicted_raw_targets = performer.estimate_metrics(raw_features)
        predicted_quality = performer.evaluate_quality(predicted_raw_targets)
        return predicted_quality
    # def generate_random_state(self):
    #     state = performer.generate_random_graph()
    #     return state
optimization = Optimization(initial_state = performer.generate_initial_graph())

def initialize(benchmark):
    performer.self_initialize(benchmark)
    actuator.initialize_files()
    performer.initialize_dataset()
    return

def design(benchmark):
    performer.self_initialize(benchmark)
    restarts = 100
    iterations = 200
    for trial in range(restarts):
        print 'design:', 'benchmark =', performer.benchmark + ';',
        print 'optimization_target =', performer.optimization_target + ';',
        print 'trial =', trial
        performer.update_estimators(performer.database[performer.benchmark]['dataset'], 4)
        final = hill_climbing(optimization, iterations_limit = iterations)
        design_instance = [datetime.now(), performer.benchmark, performer.optimization_target,
                           to_dict_of_dicts(final.state)]
        with open(performer.database[performer.benchmark]['design'], 'a') as f:
            f.write('\t'.join(map(str, design_instance)) + '\n')
    return

def analyze(benchmark):
    performer.self_initialize(benchmark)
    performer.analyze_designs('freenet')
    # for interest in ['trace', 'result', 'links']:
    # for interest in ['trace']:
    #     actuator.visualize(benchmark, interest)
    return

def evaluate_mesh():
    for benchmark in performer.benchmarks:
        performer.self_initialize(benchmark)
        performer.generate_design_mesh()
        performer.analyze_designs('mesh')
    return

def visualize(dataframe, figure, ylabel):
    print dataframe
    axis = dataframe.plot()
    axis.set_ylabel(ylabel)
    axis.get_figure().savefig(figure)
    # axis = visual.plot(kind = 'bar')
    return

def compare(dataframe, index, columns, values, figure_file):
    feature = dataframe[[index, columns, values]]
    print feature
    feature = feature.pivot(index, columns, values)
    visualize(feature, figure_file, values)
    return

def summarize(metrics):
    full_metrics = ['real_latency', 'real_power', 'real_latency_power_product']
    results = DataFrame()
    for architecture in ['mesh', 'freenet']:
        stats_file = 'stats_' + architecture
        for benchmark in performer.benchmarks:
            data = read_csv(performer.database[benchmark][stats_file], sep = '\t', skipinitialspace = True)
            record = data.ix[data[metrics].idxmin()]
            record.insert(1, 'architecture', architecture)
            results = results.append(record, ignore_index = True)
    results['weight'] = 'weight'
    results['graph'] = map(performer.string_to_graph, results['topology'])
    results['average_hop_count'] = map(average_shortest_path_length, results['graph'])
    results['average_path_length'] = results['path_length']*4/9
    results.to_csv(performer.stats[architecture], sep = '\t', index = False)
    print results.columns.values
    
    degree = results[results['architecture'] == 'freenet'][['benchmark', 'degree_average', 'degree_max']]
    degree.set_index('benchmark', inplace = True)
    visualize(degree, performer.image['degree'], 'degree')

    edge_weight = results[results['architecture'] == 'freenet'][['benchmark','edge_weight_distribution']]
    compare(results, 'benchmark', 'architecture', 'average_path_length', performer.image['average_path_length'])
    compare(results, 'benchmark', 'architecture', 'real_latency', performer.image['latency'])
    compare(results, 'benchmark', 'architecture', 'average_hop_count', performer.image['average_hop_count'])

    # results['network_figure'] = map(performer.get_network_figure, results['benchmark'])
    # freenet_topologies = results[results['architecture'] == 'freenet']
    # map(actuator.draw_graph, freenet_topologies['benchmark'],
    #     freenet_topologies['topology'], freenet_topologies['network_figure'])
    return

if __name__ == '__main__':
    pool = Pool(8)
    # pool.map(initialize, performer.benchmarks)
    pool.map(design, performer.benchmarks)
    # pool.map(analyze, performer.benchmarks)
    # evaluate_mesh()
    # summarize(['power'])
