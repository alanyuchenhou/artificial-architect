#!/usr/bin/env python

from os import devnull
from pprint import pprint
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
from networkx import shortest_path_length
from networkx import average_shortest_path_length
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

# data_file = 'web-Google_sorted'
# with open(data_file + ".csv", 'r') as old_data:
#     with open(data_file + ".final.csv", 'w') as new_data:
#         data_reader = reader(old_data)
#         data_writer = writer(new_data)
#         for record in data_reader:
#             thread_count = float(record[3])
#             if thread_count == 1:
#                 singlethread_runtime = float(record[4])
#                 speedup = 1
#             else:
#                 multithread_runtime = float(record[4])
#                 speedup = singlethread_runtime / multithread_runtime
#             record.append(' ' + str(speedup))
#             data_writer.writerow(record)

from time import strftime
from itertools import cycle
from subprocess import check_call
from subprocess import call
from csv import reader
from csv import writer
from numpy import genfromtxt
from numpy import delete
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
from matplotlib.pyplot import gca
from matplotlib.pyplot import plot
from matplotlib.pyplot import subplot
from matplotlib.pyplot import legend
from matplotlib.pyplot import axis
from matplotlib.pyplot import yscale
from matplotlib.pyplot import grid
from matplotlib.pyplot import ylabel
from matplotlib.pyplot import xlabel
from matplotlib.pyplot import show
from matplotlib.pyplot import savefig
from matplotlib.pyplot import plotfile
from matplotlib.font_manager import FontProperties
BENCHMARKS = ['bodytrack', 'canneal', 'dedup', 'fluidanimate', 'freqmine', 'swaption', 'vips']
benchmark = BENCHMARKS[0]
DATASET = 'dataset.' + benchmark + '.dat'
FIGURE = 'trace-' + benchmark + '.png'
DOCUMENT = 'architect'
def archive():
    time_stamp = strftime('-%Y-%m-%d')
    check_call(['cp', FIGURE, FIGURE.replace('.', time_stamp + '.')])
def analyze():
    raw_data = genfromtxt(DATASET, names = True)
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
    savefig(FIGURE)
    check_call(['pdflatex', DOCUMENT])

# archive()
analyze()
