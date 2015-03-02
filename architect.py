#!/usr/bin/env python
# simulator bugs: link length ignored; power components missing
from collections import OrderedDict
from multiprocessing import Pool
from shutil import copyfile
from ast import literal_eval
from os import devnull
from os import rename
from pprint import pprint
from shutil import copy
from cProfile import run
from fileinput import input
from itertools import combinations
from functools import reduce
from operator import mul
from random import uniform
from random import choice
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
from networkx import DiGraph
from networkx import relabel_nodes
from networkx import nodes
from networkx import get_node_attributes
from networkx import get_edge_attributes
from networkx import neighbors
from networkx import is_connected
from networkx import is_strongly_connected
from networkx import diameter
from networkx import radius
from networkx import degree
from networkx import density
from networkx import draw
from networkx import draw_networkx_edge_labels
from networkx import complete_graph
from networkx import gnm_random_graph
from networkx import grid_2d_graph
from networkx import connected_watts_strogatz_graph
from networkx import navigable_small_world_graph
from networkx import to_numpy_matrix
from networkx import from_numpy_matrix
from networkx import to_dict_of_dicts
from networkx import to_edgelist
from networkx import shortest_path
from networkx import shortest_path_length
from networkx import average_shortest_path_length
from networkx import average_clustering
import numpy
from numpy import loadtxt
from numpy import savetxt
from numpy import delete
from numpy import arange
from numpy import asarray
from numpy import histogram
from numpy import zeros
from numpy import array
from numpy import full
from numpy import empty
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
from numpy.linalg import norm
from numpy.random import rand
from numpy.random import randn
from scipy.spatial.distance import cityblock
from scipy.stats import rv_discrete
from pandas import read_csv
from pandas import DataFrame
from pandas import Series
from pandas import concat
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
from matplotlib.pyplot import title
from matplotlib.pyplot import savefig

class Critic(object):
    def evaluate_kernels(self, dataset):
        data = actuator.load_data(dataset, range(Performer.SAMPLE_COUNT))
        kernels = ['linear', 'poly', 'rbf', 'sigmoid']
        for kernel in kernels:
            svr = SVR(kernel)
            parameters = {'C':logspace(0, 2, 3).tolist()}
            if kernel == 'poly':
                parameters['degree'] = linspace(1, 4, 4, dtype = int).tolist()
            if kernel == 'rbf':
                parameters['gamma'] = logspace(-4, 0, 5).tolist()
            estimator = GridSearchCV(svr, parameters, cv = 10, n_jobs = -1)
            estimator.fit(data[2][:-10], data[1][:-10])
            print 'kernel=', kernel,
            print 'best_params=', estimator.best_params_,
            print 'best_score=', estimator.best_score_
        return
class Performer(object):
    random_edge_generator = None
    scaler = StandardScaler()
    estimators = []
    DIMENSION = 2
    RADIX = 8
    DEGREE_MAX = 8
    NODE_COUNT = RADIX ** DIMENSION
    EDGE_COUNT = int(NODE_COUNT * 2)
    LOG = 'thread.log'
    BENCHMARKS = ['fft', 'lu', 'radix', 'water', 'canneal', 'dedup', 'fluidanimate', 'vips']
    BENCHMARK = None
    OPTIMIZATION_TARGET = None
    TOTAL_TRAFFIC = {}
    TRAFFIC = {}
    INITIAL_DATASET_SIZE = 10
    TARGETS = ['latency', 'energy']
    TARGET_TOKENS = ['Avg. Message Latency:', 'Average energy per message done:']
    FEATURES = ['average_clustering', 'average_hop_count', 'weighted_average_hop_count', 'average_link_length',
                     'average_degree', 'max_degree', 'edge_count', 'total_traffic']
    ATTRIBUTES = TARGETS + FEATURES
    NORMALIZED_ATTRIBUTES = ['normalized_' + a  for a in ATTRIBUTES]
    def extract_features(self, graph):
        print 'performer.extract_features:'
        raw_features = [average_clustering(graph), average_shortest_path_length(graph),
                        self.weighted_average_path_length(self.TRAFFIC[self.BENCHMARK], graph),
                        average(get_edge_attributes(graph, 'length').values()), average(graph.degree().values()),
                        max(graph.degree().values()), graph.number_of_edges(), self.TOTAL_TRAFFIC[self.BENCHMARK]]
        return raw_features
    def position(self, node_index):
        node_position = (node_index / self.RADIX, node_index % self.RADIX)
        return node_position
    def link_length(self, source, destination):
        return cityblock(self.position(source), self.position(destination))
    def edge_index(self, source, destination):
        index = source * self.NODE_COUNT + destination
        return index
    def edge_nodes(self, index):
        nodes = (index / self.NODE_COUNT, index % self.NODE_COUNT)
        return nodes
    def file_name(self, quantity, index):
        temp_name = quantity + '_' + index
        if quantity in ['network_figure','hop_counts','link_lengths'] + self.ATTRIBUTES + self.NORMALIZED_ATTRIBUTES:
            name = temp_name
        elif quantity in ['design', 'dataset']:
            name = temp_name + '.tsv'
        else:
            raise NameError('no file for quantity: ' + quantity)
        return name
    def reset(self, benchmark, optimization_target):
        if (benchmark not in self.BENCHMARKS):
            raise NameError('unknown benchmark: ' + benchmark)
        self.BENCHMARK = benchmark
        if (optimization_target not in self.TARGETS):
            raise NameError('unknown optimization_target: ' + optimization_target)
        self.OPTIMIZATION_TARGET = optimization_target
        print 'performer.reset:', self.BENCHMARK, self.OPTIMIZATION_TARGET, self.NODE_COUNT, self.EDGE_COUNT
    def initialize(self, radix):
        self.RADIX = radix
        self.NODE_COUNT = self.RADIX ** self.DIMENSION
        self.EDGE_COUNT = int(self.NODE_COUNT * 2)
        distances = zeros((self.NODE_COUNT, self.NODE_COUNT))
        edge_indices = zeros((self.NODE_COUNT, self.NODE_COUNT), int)
        for node1 in range(self.NODE_COUNT):
            for node2 in range(self.NODE_COUNT):
                distances[node1][node2] = cityblock(self.position(node1), self.position(node2))
                edge_indices[node1][node2] = self.edge_index(node1, node2)
        alpha = distances**(-1.8)
        fill_diagonal(alpha, 0)
        for benchmark in self.BENCHMARKS:
            if radix == 8:
                raw_traffic = loadtxt('traffic_' + benchmark + '.tsv')
            else:
                raw_traffic = rand(self.NODE_COUNT,self.NODE_COUNT)
            raw_traffic +=  raw_traffic.transpose()
            self.TOTAL_TRAFFIC[benchmark] = raw_traffic.sum().sum()
            self.TRAFFIC[benchmark] = raw_traffic
            # raw_probabilities = raw_traffic * alpha
            raw_probabilities = raw_traffic
            probabilities = raw_probabilities / (raw_probabilities.sum().sum())
            self.random_edge_generator = rv_discrete(name = 'custm',values = (edge_indices,probabilities))
        print 'performer.initialize:', self.TOTAL_TRAFFIC
        return
    def update_estimators(self, accuracy):
        data = self.load_data(self.file_name('dataset',self.BENCHMARK), range(len(performer.ATTRIBUTES)))
        c_range = accuracy
        gamma_range = accuracy
        parameters = {'C' : logspace(0, c_range, c_range+1).tolist(),
                      'gamma' : logspace(- gamma_range, 0, gamma_range+1).tolist()}
        estimators = []
        svrs = []
        data_instance = [datetime.now(), self.BENCHMARK]
        for i in range(len(self.TARGETS)):
            svrs.append(SVR('rbf'))
            estimators.append(GridSearchCV(svrs[i], parameters, n_jobs = -1))
            estimators[i].fit(data[len(self.TARGETS)], data[i])
            data_instance += [estimators[i].best_params_, estimators[i].best_score_]
        print  'performer: update_estimator: benchmark =', performer.BENCHMARK+';', data_instance
        with open(self.file_name('accuracy', self.BENCHMARK), 'a') as f:
            f.write('\t'.join(map(str, data_instance)) + '\n')
        self.estimators = estimators
        return
    def center(self, graph, source, destination):
        center = [source, destination]
        for i in range(self.DIMENSION):
            center[i] = .5*(graph.node[source]['position'][i] + graph.node[destination]['position'][i])
        return center
    def constraints_satisfied(self, graph):
        degree_max = max(graph.degree().values())
        # print 'performer.constraints_satisfied:', degree_max, graph.number_of_edges(), is_connected(graph)
        if graph.number_of_edges() <= self.EDGE_COUNT and degree_max <= self.DEGREE_MAX and is_connected(graph):
            return True
        else:
            return False
    def process_graph(self, graph):
        graph.remove_edges_from(graph.selfloop_edges())
        for node_key, node_attributes in graph.nodes(data=True):
            node_attributes['position'] = self.position(node_key)
        for source, destination, edge_attributes in graph.edges(data=True):
            edge_attributes['length'] = self.link_length(source, destination)
        return
    def key_mapping(self, tuple_key):
        new_key = tuple_key[0] * self.RADIX + tuple_key[1]
        return new_key
    def generate_grid_graph(self):
        print 'performer.generate_grid_graph:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT
        tuple_keyed_graph = grid_2d_graph(self.RADIX, self.RADIX)
        graph = relabel_nodes(tuple_keyed_graph, self.key_mapping)
        self.process_graph(graph)
        return graph
    def generate_random_graph(self):
        print 'performer.generate_random_graph:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT
        while True:
            graph = gnm_random_graph(self.NODE_COUNT, self.EDGE_COUNT)
            if self.constraints_satisfied(graph):
                self.process_graph(graph)
                return graph
    def generate_small_world_graph(self):
        print 'performer.generate_small_world_graph:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT
        while True:
            graph = Graph()
            for i in range(self.NODE_COUNT):
                graph.add_node(i)
            while graph.number_of_edges() < self.EDGE_COUNT:
                source, destination = self.edge_nodes(self.random_edge_generator.rvs())
                graph.add_edge(source, destination, length = self.link_length(source, destination))
            if self.constraints_satisfied(graph):
                self.process_graph(graph)
                return graph
    def weighted_average_path_length(self, traffic, graph):
        # print 'performer.weighted_average_path_length:'
        raw_path_lengths = shortest_path_length(graph)
        path_lengths = zeros((self.NODE_COUNT, self.NODE_COUNT))
        for source in raw_path_lengths:
            for destination in raw_path_lengths[source]:
                path_lengths[source][destination] = raw_path_lengths[source][destination]
        weighted_average = average(path_lengths, weights = traffic)
        return weighted_average
    def load_data(self, dataset, columns):
        raw_dataset = loadtxt(dataset, usecols = columns, skiprows = 1)
        self.scaler.fit(raw_dataset)
        scaled_dataset = self.scaler.transform(raw_dataset)
        split_dataset = map(squeeze, hsplit(scaled_dataset, range(1,len(self.TARGETS)+1)))
        return split_dataset
    def estimate_metrics(self, raw_features):
        raw_sample = asarray(range(len(self.TARGETS)) + raw_features)
        scaled_sample = self.scaler.transform(raw_sample)
        for i in range(len(self.TARGETS)):
            scaled_sample[i] = (self.estimators[i].predict(scaled_sample[len(self.TARGETS):])).tolist()[0]
        estimated_raw_sample = self.scaler.inverse_transform(asarray(scaled_sample)).tolist()
        estimated_metrics = estimated_raw_sample[:len(self.TARGETS)]
        return estimated_metrics
    def evaluate_quality(self, raw_targets):
        if self.OPTIMIZATION_TARGET == 'latency_energy_product':
            return -(raw_targets[0] * raw_targets[1])
        elif self.OPTIMIZATION_TARGET == 'latency':
            return -raw_targets[0]
        elif self.OPTIMIZATION_TARGET == 'energy':
            return -raw_targets[1]
        else:
            raise NameError('unknown optimization_target')
    def add_data(self, initial, graph, metrics):
        real_latency_energy_product = prod(metrics)
        raw_features = self.extract_features(graph)
        estimated_metrics = metrics
        if initial == False:
            estimated_metrics = self.estimate_metrics(raw_features)
        estimated_latency_energy_product = prod(estimated_metrics)
        data_instance = metrics + raw_features + estimated_metrics
        data_instance += [real_latency_energy_product, estimated_latency_energy_product]
        print 'performer: add_data:', 'benchmark =', self.BENCHMARK + ';', data_instance
        with open(self.file_name('dataset', None), 'a') as f:
            f.write('\t'.join(map(str, data_instance)) + '\n')
        return
    def initialize_dataset(self, thread_log):
        for index in range(self.INITIAL_DATASET_SIZE):
            print 'performer.initialize_dataset:', thread_log, index
            graph = self.generate_small_world_graph()
            metrics = performer.evaluate_metrics(graph, thread_log)
            self.add_data(True, graph, metrics)
        return
    def string_to_graph(self, graph_string):
        # print 'performer: string_to_graph: graph_string =', graph_string
        graph = Graph(literal_eval(graph_string))
        performer.process_graph(graph)
        return graph
    def evaluate_metrics(self, graph, thread_log):
        actuator.configure_topology(graph)
        with open(thread_log, 'w+') as f:
            check_call([actuator.SIMULATOR, self.BENCHMARK], stdout = f)
        metrics = sensor.extract_targets(thread_log)
        print 'performer.evaluate_metrics:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT, metrics
        return metrics
    def add_design_instance(self, architecture, graph, metrics):
        design_instance = [datetime.now(), architecture, self.BENCHMARK,
                           self.OPTIMIZATION_TARGET, to_dict_of_dicts(graph)] + metrics
        with open(self.file_name('design', ''), 'a') as f:
            f.write('\t'.join(map(str, design_instance)) + '\n')
        return
performer = Performer()

class Sensor(object):
    def extract_targets(self, thread_log):
        target_values = list(performer.TARGET_TOKENS)
        with open(thread_log, 'r') as f:
            for line in f:
                for index in range(len(performer.TARGET_TOKENS)):
                    if line.startswith(performer.TARGET_TOKENS[index]):
                        target_values[index] = float(line.replace(performer.TARGET_TOKENS[index], ''))
        return target_values
sensor = Sensor()
    
class Actuator(object):
    SIMULATOR = 'simulator.out'
    TOPOLOGY = 'topology.tsv'
    def configure_topology(self, graph):
        # print 'actuator.configure_topology:', performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
        adjacency = to_numpy_matrix(graph, dtype = int, nonedge = -1)
        # fill_diagonal(adjacency, 0)
        # print adjacency.astype(int)
        all_disconnected = full((performer.NODE_COUNT, performer.NODE_COUNT), -1, int)
        side = full((performer.NODE_COUNT, performer.NODE_COUNT), -1, int)
        fill_diagonal(side, 2)
        configuration = hstack((vstack((all_disconnected, side)), vstack((side, adjacency))))
        configuration = configuration.astype(int)
        savetxt(self.TOPOLOGY, configuration, fmt='%d', delimiter = '\t')
        return
    def initialize_files(self):
        columns = (['real_' + s for s in performer.TARGETS] + performer.FEATURES
                           + ['estimated_' + s for s in performer.TARGETS]
                           + ['real_latency_energy_product', 'estimated_latency_energy_product'])
        with open(performer.file_name('dataset', ''), 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        columns = ['time', 'architecture', 'benchmark', 'optimization_target', 'topology'] + performer.TARGETS
        with open(performer.file_name('design', ''), 'w+') as f:
            f.write('\t'.join(map(str, columns)) + '\n')
        return
    def draw_graph(self, benchmark, graph, figure_file):
        figure()
        title(benchmark)
        draw(graph, get_node_attributes(graph, 'position'), hold = True)
        # draw_networkx_edge_labels(graph, get_node_attributes(graph, 'position'), alpha = 0.2)
        savefig(figure_file)
        return
    def plot_bar(self, dataframe, index, columns, values):
        data = dataframe[[index, columns, values]]
        print 'actuator: plot_line: ', index, columns, values
        data = data.pivot(index, columns, values)
        # print data
        axis = data.plot(kind = 'bar', edgecolor = 'none')
        axis.set_ylabel(values)
        axis.get_figure().savefig(performer.file_name(values, index))
        return
    def plot_histogram(self, dataframe, column, value, benchmark):
        figure()
        distributions = DataFrame()
        for index1, row in dataframe.iterrows():
            bin_count = max(row[value]) + 3
            if value == 'link_lengths':
                count = 112
            else:
                count = -1
            new_column = DataFrame({row[column]: Series(histogram(row[value][:count], bins = range(bin_count))[0])})
            distributions = concat([distributions, new_column], axis = 1)
        print 'actuator: plot_histogram: ', column, value
        axis = distributions.plot(kind = 'bar', edgecolor = 'none')
        axis.set_xlabel(value)
        axis.get_figure().savefig(performer.file_name(value, benchmark))
        return
actuator = Actuator()

class Optimization(SearchProblem):
    def actions(self, state):
        successors = []
        successor1 = state.copy()
        victim = choice(successor1.edges())
        successor1.remove_edge(victim[0], victim[1])
        for source in state.nodes():
            for destination in state.nodes():
                successor = successor1.copy()
                successor.add_edge(source, destination, length = performer.link_length(source, destination))
                successor.remove_edges_from(successor.selfloop_edges())
                if performer.constraints_satisfied(successor):
                    successors.append(successor)
        print 'optimization: actions: successor_count:', len(successors)
        return successors
    def result(self, state, action):
        return action
    def value(self, state):
        raw_features = performer.extract_features(state)
        estimated_metrics = performer.estimate_metrics(raw_features)
        estimated_quality = performer.evaluate_quality(estimated_metrics)
        return estimated_quality

def design_freenet(thread_log):
    restarts = 10
    for trial in range(restarts):
        print 'design_freenet:', performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
        print 'trial =', trial
        performer.update_estimators(4)
        optimization = Optimization(initial_state = performer.generate_small_world_graph())
        final = hill_climbing(optimization, iterations_limit = 200)
        graph = final.state
        metrics = performer.evaluate_metrics(graph, thread_log)
        self.add_data(True, graph, metrics)
        performer.add_design_instance('freenet', graph, metrics)
    return

def design_mesh():
    print 'design_mesh:', performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
    graph = performer.generate_grid_graph()
    metrics = performer.evaluate_metrics(graph, performer.LOG)
    performer.add_design_instance('mesh', graph, metrics)
    return

def design_small_world():
    print 'design_small_world:' + performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
    graph = performer.generate_small_world_graph()
    metrics = performer.evaluate_metrics(graph, performer.LOG)
    performer.add_design_instance('small_world', graph, metrics)
    return

def design_test():
    print 'test_small_world:' + performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
    raw_topology = loadtxt('topology_test.tsv', int)[-64:, -64:]
    graph = from_numpy_matrix(raw_topology)
    print performer.extract_features(graph)
    metrics = performer.evaluate_metrics(graph, performer.LOG)
    performer.add_design_instance('test_small_world', graph, metrics)
    return

def view():
    result = DataFrame()
    metrics = ['latency', 'energy', 'latency_energy_product']
    for benchmark in performer.BENCHMARKS:
        data = read_csv(performer.file_name('design', benchmark), sep = '\t', skipinitialspace = True)
        data['latency_energy_product'] = data['latency'] * data['energy']
        evolution = data.cummin()
        evolution = data
        evolution['trial'] = evolution.index
        result=result.append(evolution[['trial', 'benchmark'] + metrics], ignore_index = True)
    for metric in metrics:
        actuator.plot_line(result, 'trial', 'benchmark', metric)
    return

def analyze():
    # metrics = ['latency', 'energy']
    metrics = ['latency']
    average_hop_count_random = 18
    average_clustering_random = 0.06
    results = DataFrame()
    data = read_csv(performer.file_name('design', ''), sep = '\t', skipinitialspace = True)
    data['graph'] = [performer.string_to_graph(t) for t in data['topology']]
    data['link_lengths'] = [get_edge_attributes(g, 'length').values() for g in data['graph']]
    data['average_link_length'] = [average(h) for h in data['link_lengths']]
    data['max_link_length'] = [max(h) for h in data['link_lengths']]
    data['total_traffic'] = [performer.TOTAL_TRAFFIC[b] for b in data['benchmark']]
    data.sort('latency', inplace = True)
    print data[['architecture', 'benchmark', 'average_link_length'] + performer.TARGETS]
    for benchmark in performer.BENCHMARKS:
        # for architecture in ['mesh', 'small_world', 'freenet']:
        for architecture in ['mesh']:
            architecture_data = data[(data['architecture'] == architecture) & (data['benchmark'] == benchmark)]
            index = architecture_data[metrics].idxmin()
            # if architecture == 'freenet':
            #     index = architecture_data[metrics].idxmin()
            # else:
            #     index = abs(architecture_data[metrics] - architecture_data[metrics].mean()).argmin()
            record = architecture_data.ix[index]
            results = results.append(record, ignore_index = True)
    results['latency_energy_product'] = results['latency'] * results['energy']
    results['edge_count'] = [g.number_of_edges() for g in results['graph']]
    results['average_clustering'] = [average_clustering(g.to_undirected()) for g in results['graph']]
    results['hop_counts'] = [[length for d in shortest_path_length(g).values()
                              for length in d.values()] for g in results['graph']]
    results['average_hop_count'] = [average(h) for h in results['hop_counts']]
    results['weighted_average_hop_count'] = [performer.weighted_average_path_length(
        performer.TRAFFIC[row['benchmark']], row['graph']) for index, row in results.iterrows()]
    results['max_hop_count'] = [max(h) for h in results['hop_counts']]
    results['small_world_ness'] = [(row['average_clustering']/row['average_hop_count'])
                                    /(average_clustering_random / average_hop_count_random)
                                    for index, row in results.iterrows()]
    results['degrees'] = [g.degree().values() for g in results['graph']]
    results['average_degree'] = [average(d) for d in results['degrees']]
    results['max_degree'] = [max(d) for d in results['degrees']]
    results['network_figure'] = [performer.file_name('network_figure', b) for b in results['benchmark']]
    results['architecture/benchmark'] = results['architecture'] + '/' + results['benchmark']
    # for index, row in results.iterrows():
    #     mask = (results['architecture'] == 'mesh') & (results['benchmark'] == row['benchmark'])
    #     factor = squeeze(results[mask]['latency'])
    #     print factor
    for normalized_attribute, attribute in zip(performer.NORMALIZED_ATTRIBUTES, performer.ATTRIBUTES):
        results[normalized_attribute] = [row[attribute]/squeeze(
                results[(results['architecture'] == 'mesh') & (results['benchmark'] == row['benchmark'])][attribute])
                                              for index, row in results.iterrows()]
    print 'analyze:', results.columns.values
    attributes = performer.TARGETS + ['total_traffic', 'average_link_length']
    # print results[['architecture', 'benchmark'] + performer.NORMALIZED_ATTRIBUTES]
    # print results[['architecture', 'benchmark'] + attributes]
    # for attribute in performer.normalized_attributes:
    #     actuator.plot_bar(results, 'benchmark', 'architecture', attribute)
    # for attribute in ['hop_counts', 'link_lengths']:
    #     for benchmark in performer.BENCHMARKS:
    #         mask = results['benchmark'] == benchmark
    #         actuator.plot_histogram(results[mask], 'architecture/benchmark', attribute, benchmark)

    # freenet_topologies = results[results['architecture'] == 'freenet']
    # map(actuator.draw_graph, freenet_topologies['benchmark'],
    #     freenet_topologies['topology'], freenet_topologies['network_figure'])
    return

def test():
    for benchmark in performer.BENCHMARKS:
    # for benchmark in ['fft']:
        performer.reset(benchmark, 'latency')
        # print performer.FEATURES
        # graph = performer.generate_grid_graph()
        # print performer.extract_features(graph)
        # raw_topology = loadtxt('topology_test.tsv', int)[-64:, -64:] + 1
        # graph = from_numpy_matrix(raw_topology)
        # performer.process_graph(graph)
        # actuator.configure_topology(graph)
        # print performer.extract_features(graph)
        # print performer.constraints_satisfied(graph)
        # design_mesh()
        design_small_world()
        # design_test()
    return

if __name__ == '__main__':
    # actuator.initialize_files()
    # thread_count = 8
    # pool = Pool(thread_count)
    # thread_logs = ['thread' + str(thread) + '.log' for thread in range(thread_count)]
    performer.initialize(8)
    # print performer.TRAFFIC['fft']
    test()
    # design_freenet()
    # view()
    analyze()
    # pool.map(design_freenet, thread_logs)
    # check_call(['pdflatex', 'architect'])
