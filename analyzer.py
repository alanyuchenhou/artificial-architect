#!/usr/bin/env python

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

# time_stamp = strftime('%Y-%m-%d-%H-%M-%S')
# check_call(['mv', TRACE, TRACE[:5] + '-' + time_stamp + TRACE[5:]])

from time import strftime
from itertools import cycle
from subprocess import check_call
from subprocess import call
from csv import reader
from csv import writer
from numpy import genfromtxt
from matplotlib import use
use('Agg')
from matplotlib.pyplot import figure
from matplotlib.pyplot import gca
from matplotlib.pyplot import plot
from matplotlib.pyplot import subplot
from matplotlib.pyplot import legend
from matplotlib.pyplot import axis
from matplotlib.pyplot import grid
from matplotlib.pyplot import ylabel
from matplotlib.pyplot import xlabel
from matplotlib.pyplot import show
from matplotlib.pyplot import savefig
from matplotlib.pyplot import plotfile
from matplotlib.font_manager import FontProperties
TRACE = 'trace.dat'
FIGURE = 'trace.png'
DOCUMENT = 'architect'

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

data = genfromtxt(TRACE, delimiter = '\t', names = True)
styles = cycle(('--', '-.', '-', ':'))
font_properties = FontProperties()
font_properties.set_size('small')
figure()
for column in data.dtype.names:
    # plot(data[column], label = column, linestyle = styles.next())
    if (column == 'score'):
        subplot(311)
        plot(data[column], label = column)
        legend(loc = 'upper right', prop = font_properties).get_frame().set_alpha(.1)
    if (column == 'latency'):
        subplot(312)
        plot(data[column], label = column)
        legend(loc = 'upper right', prop = font_properties).get_frame().set_alpha(.1)
    if (column == 'path_length'):
        subplot(313)
        plot(data[column], label = column)
        legend(loc = 'upper right', prop = font_properties).get_frame().set_alpha(.1)
xlabel('step')
# legend(loc = 'upper right', prop = font_properties).get_frame().set_alpha(.1)
savefig(FIGURE, dpi = 200)
check_call(['pdflatex', DOCUMENT])
