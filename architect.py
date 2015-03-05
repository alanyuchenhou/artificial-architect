#!/usr/bin/env python
# simulator bugs: power components missing
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
from subprocess import call
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
from scipy.spatial.distance import euclidean
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
        data = actuator.load_data(dataset, range(performer.SAMPLE_COUNT))
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
    SIMULATOR = 'simulator.out'
    DATASET = 'dataset.tsv'
    NODE_WEIGHT = 3
    DIMENSION = 2
    DEGREE_MAX = 7
    BENCHMARKS = ['fft', 'lu', 'radix', 'water', 'canneal', 'dedup', 'fluidanimate', 'vips']
    TARGETS = ['latency', 'energy']
    TARGET_TOKENS = ['Avg. Message Latency:', 'Average energy per message done:']
    FEATURES = ['average_path_length',
                'weighted_average_path_length',
                'average_link_length',
                'max_link_length',
                'min_link_length',
                'average_degree',
                'max_degree',
                'min_degree',
                'edge_count',
                'average_clustering',
                'small_world_ness',
                'total_traffic']
    ATTRIBUTES = TARGETS + FEATURES
    NORMALIZED_ATTRIBUTES = ['normalized_' + a  for a in ATTRIBUTES]
    METADATA = ['time', 'architecture', 'benchmark', 'optimization_target', 'topology']
    def extract_features(self, graph):
        # print 'performer.extract_features:'
        raw_features = [average_shortest_path_length(graph, 'weight'),
                        self.weighted_average_path_length(self.TRAFFIC, graph),
                        average(get_edge_attributes(graph, 'length').values()),
                        max(get_edge_attributes(graph, 'length').values()),
                        min(get_edge_attributes(graph, 'length').values()),
                        average(graph.degree().values()),
                        max(graph.degree().values()),
                        min(graph.degree().values()),
                        graph.number_of_edges(),
                        average_clustering(graph),
                        average_clustering(graph) / average_shortest_path_length(graph, 'weight'),
                        self.TOTAL_TRAFFIC]
        return raw_features
    def position(self, node_index):
        node_position = (node_index / self.RADIX, node_index % self.RADIX)
        return node_position
    def link_length(self, source, destination):
        return int(euclidean(self.position(source), self.position(destination)))
    def edge_weight(self, source, destination):
        return self.link_length(source, destination) + self.NODE_WEIGHT
    def edge_index(self, source, destination):
        index = source * self.NODE_COUNT + destination
        return index
    def edge_nodes(self, index):
        nodes = (index / self.NODE_COUNT, index % self.NODE_COUNT)
        return nodes
    def file_name(self, quantity, index):
        if quantity in ['network_figure', 'link_lengths'] + self.ATTRIBUTES + self.NORMALIZED_ATTRIBUTES:
            name = quantity + '_' + str(index)
        else:
            raise NameError('no file for quantity: ' + quantity)
        return name
    def initialize(self, radix, edge_count):
        self.RADIX = radix
        self.NODE_COUNT = self.RADIX ** self.DIMENSION
        self.EDGE_COUNT = edge_count
        return
    def reinitialize(self, thread_id, benchmark, optimization_target, beta):
        if (benchmark not in self.BENCHMARKS):
            raise NameError('unknown benchmark: ' + benchmark)
        if (optimization_target not in self.TARGETS):
            raise NameError('unknown optimization_target: ' + optimization_target)
        self.BENCHMARK = benchmark
        self.TRAFFIC_FILE = 'traffic_' + benchmark + '.tsv'
        self.THREAD_ID = thread_id
        self.TOPOLOGY = 'topology' + str(thread_id) +'.tsv'
        self.SIMULATION_LOG = 'simulation' + str(thread_id) + '.log'
        self.OPTIMIZATION_TARGET = optimization_target
        distances = zeros((self.NODE_COUNT, self.NODE_COUNT))
        edge_indices = zeros((self.NODE_COUNT, self.NODE_COUNT), int)
        for node1 in range(self.NODE_COUNT):
            for node2 in range(self.NODE_COUNT):
                distances[node1][node2] = self.edge_weight(node1, node2)
                edge_indices[node1][node2] = self.edge_index(node1, node2)
        alpha = distances**(-beta)
        fill_diagonal(alpha, 0)
        if self.RADIX == 8:
            raw_traffic = loadtxt(self.TRAFFIC_FILE)
        else:
            raw_traffic = rand(self.NODE_COUNT,self.NODE_COUNT)
        raw_traffic +=  raw_traffic.transpose()
        self.TOTAL_TRAFFIC = raw_traffic.sum().sum()
        self.TRAFFIC = raw_traffic
        # raw_probabilities = raw_traffic * alpha
        raw_probabilities = alpha
        probabilities = raw_probabilities / (raw_probabilities.sum().sum())
        self.random_edge_generator = rv_discrete(name = 'custm', values = (edge_indices, probabilities))
        print 'performer.initialize:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT, self.TOTAL_TRAFFIC
        return
    def update_estimators(self, accuracy):
        data = self.load_data(self.DATASET, range(len(self.ATTRIBUTES)))
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
        print  'performer: update_estimator: benchmark =', self.BENCHMARK+';', data_instance
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
            edge_attributes['weight'] = self.edge_weight(source, destination)
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
                graph.add_edge(source, destination, length = self.link_length(source, destination),
                               weight = self.edge_weight(source, destination))
                if max(graph.degree().values()) > self.DEGREE_MAX:
                    graph.remove_edge(source, destination)
            if self.constraints_satisfied(graph):
                self.process_graph(graph)
                return graph
    def weighted_average_path_length(self, traffic, graph):
        # print 'performer.weighted_average_path_length:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT
        raw_path_lengths = shortest_path_length(graph, weight = 'weight')
        path_lengths = zeros((self.NODE_COUNT, self.NODE_COUNT))
        for source in raw_path_lengths:
            for destination in raw_path_lengths[source]:
                path_lengths[source][destination] = raw_path_lengths[source][destination]
        weighted_average = average(path_lengths, weights = traffic)
        return weighted_average
    def load_data(self, dataset, columns):
        raw_dataset = loadtxt(dataset, usecols = columns, skiprows = 1)
        self.scaler = StandardScaler()
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
        if self.OPTIMIZATION_TARGET == 'latency':
            return -raw_targets[0]
        elif self.OPTIMIZATION_TARGET == 'energy':
            return -raw_targets[1]
        else:
            raise NameError('unknown optimization_target')
    def extract_targets(self):
        target_values = [None] * len(performer.TARGETS)
        with open(self.SIMULATION_LOG, 'r') as f:
            for line in f:
                for index in range(len(performer.TARGET_TOKENS)):
                    if line.startswith(performer.TARGET_TOKENS[index]):
                        target_values[index] = float(line.replace(performer.TARGET_TOKENS[index], ''))
        return target_values
    def evaluate_metrics(self, graph):
        self.configure_topology(graph)
        with open(self.SIMULATION_LOG, 'w+') as f:
            call([self.SIMULATOR, self.BENCHMARK, self.TOPOLOGY], stdout = f)
        metrics = self.extract_targets()
        print 'performer.evaluate_metrics:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT, metrics
        return metrics
    def string_to_graph(self, graph_string):
        # print 'performer: string_to_graph: graph_string =', graph_string
        graph = Graph(literal_eval(graph_string))
        self.process_graph(graph)
        return graph
    def add_data(self, architecture, graph, metrics):
        print 'performer.add_data:', self.BENCHMARK, metrics
        metadata = [datetime.now(), architecture, self.BENCHMARK, self.OPTIMIZATION_TARGET, to_dict_of_dicts(graph)]
        design_instance = metrics + self.extract_features(graph) + metadata
        with open(self.DATASET, 'a') as f:
            f.write('\t'.join(map(str, design_instance)) + '\n')
        return
    def configure_topology(self, graph):
        # print 'performer.configure_topology:', self.BENCHMARK, self.NODE_COUNT, self.EDGE_COUNT
        adjacency = to_numpy_matrix(graph, dtype = int, nonedge = -1)
        # print adjacency.astype(int)
        all_disconnected = full((self.NODE_COUNT, self.NODE_COUNT), -1, int)
        side = full((self.NODE_COUNT, self.NODE_COUNT), -1, int)
        fill_diagonal(side, 2)
        configuration = hstack((vstack((all_disconnected, side)), vstack((side, adjacency))))
        configuration = configuration.astype(int)
        savetxt(self.TOPOLOGY, configuration, fmt='%d', delimiter = '\t')
        return
    def initialize_files(self):
        columns = self.ATTRIBUTES + self.METADATA
        with open(self.DATASET, 'w+') as f:
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
        print 'performer.plot_line: ', index, columns, values
        data = data.pivot(index, columns, values)
        # print data
        axis = data.plot(kind = 'bar', edgecolor = 'none')
        axis.set_ylabel(values)
        axis.get_figure().savefig(self.file_name(values, index))
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
        print 'performer.plot_histogram: ', column, value
        axis = distributions.plot(kind = 'bar', edgecolor = 'none')
        axis.set_xlabel(value)
        axis.get_figure().savefig(self.file_name(value, benchmark))
        return
    def view(self, data):
        result = DataFrame()
        attributes = ['benchmark'] + self.TARGETS
        for benchmark in self.BENCHMARKS:
            evolution = data[data['benchmark'] == benchmark][attributes].cummin().reindex()
            evolution['trial'] = evolution.index
            result=result.append(evolution, ignore_index = True)
        for metric in self.TARGETS:
            self.plot_line(result, 'trial', 'benchmark', metric)
        return
performer = Performer()

class Optimization(SearchProblem):
    def actions(self, state):
        successors = []
        successor1 = state.copy()
        victim = choice(successor1.edges())
        successor1.remove_edge(victim[0], victim[1])
        for source in state.nodes():
            for destination in state.nodes():
                successor = successor1.copy()
                successor.add_edge(source, destination, length = performer.link_length(source, destination),
                                   wight = performer.edge_weight(source, destination))
                successor.remove_edges_from(successor.selfloop_edges())
                if performer.constraints_satisfied(successor):
                    successors.append(successor)
        print 'optimization.actions: successor_count:', len(successors)
        return successors
    def result(self, state, action):
        return action
    def value(self, state):
        # raw_features = performer.extract_features(state)
        # estimated_metrics = performer.estimate_metrics(raw_features)
        # estimated_quality = performer.evaluate_quality(estimated_metrics)
        # return estimated_quality
        return weighted_average_path_length(state, 'weight')
def analyze():
    data = read_csv(performer.DATASET, sep = '\t', skipinitialspace = True)
    attributes = performer.METADATA + performer.ATTRIBUTES
    print 'analyze:', data.columns.values
    data['graph'] = [performer.string_to_graph(t) for t in data['topology']]
    data['link_lengths'] = [get_edge_attributes(g, 'length').values() for g in data['graph']]
    data['network_figure'] = [performer.file_name('network_figure', b) for b in data['benchmark']]
    data['architecture/benchmark'] = data['architecture'] + '/' + data['benchmark']
    data.sort('benchmark', inplace = True)
    print data[['architecture', 'benchmark', 'latency']]
    results = data.ix[data.groupby(['benchmark', 'architecture'])['latency'].idxmin()]
    for normalized_attribute, attribute in zip(performer.NORMALIZED_ATTRIBUTES, performer.ATTRIBUTES):
        normlized_values = []
        for index, row in results.iterrows():
            mesh_index = (results['architecture'] == 'mesh') & (results['benchmark'] == row['benchmark'])
            normlized_values.append(row[attribute]/squeeze(results[mesh_index][attribute]))
        results[normalized_attribute] = normlized_values
    # for attribute in performer.NORMALIZED_ATTRIBUTES:
    #     performer.plot_bar(results, 'benchmark', 'architecture', attribute)
    # for benchmark in performer.BENCHMARKS:
    #     mask = results['benchmark'] == benchmark
    #     performer.plot_histogram(results[mask], 'architecture/benchmark', 'link_lengths', benchmark)
    # freenet_topologies = results[results['architecture'] == 'freenet']
    # map(performer.draw_graph, freenet_topologies['benchmark'],
    #     freenet_topologies['topology'], freenet_topologies['network_figure'])
    return

def test():
    performer.reinitialize('lu', 'latency', 1)
    print performer.FEATURES
    for f in ['topology_test.tsv', 'topology.tsv']:
        raw_topology = loadtxt(f, int)[-64:, -64:]
        graph = from_numpy_matrix(raw_topology + 1)
        performer.process_graph(graph)
        print performer.extract_features(graph)
    return

def design(thread_id):
    architecture = 'small_world'
    benchmark = performer.BENCHMARKS[thread_id]
    performer.reinitialize(thread_id, benchmark, 'latency', uniform(0, 10))
    print 'design:', architecture, performer.BENCHMARK, performer.NODE_COUNT, performer.EDGE_COUNT
    if architecture == 'mesh':
        graph = performer.generate_grid_graph()
    elif architecture == 'random':
        graph = performer.generate_random_graph()
    elif architecture == 'small_world':
        graph = performer.generate_small_world_graph()
    elif architecture == 'test':
        raw_topology = loadtxt('topology_test.tsv', int)[-64:, -64:] + 1
        graph = from_numpy_matrix(raw_topology)
        performer.process_graph(graph)
    elif architecture == 'freenet':
        # performer.update_estimators(4)
        optimization = Optimization(initial_state = performer.generate_random_graph())
        final = hill_climbing(optimization, iterations_limit = 200)
        graph = final.state
    metrics = performer.evaluate_metrics(graph)
    if metrics[0] != None:
        performer.add_data(architecture, graph, metrics)
    return

if __name__ == '__main__':
    # performer.initialize_files()
    performer.initialize(8, 112)
    thread_count = 8
    pool = Pool(thread_count)
    # while True:
    #     pool.map(design, range(thread_count))
    # for thread_id in range(thread_count):
    #     design(thread_id)
    # test()
    analyze()
    # check_call(['pdflatex', 'architect'])
