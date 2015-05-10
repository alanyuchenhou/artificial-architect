artificial-architect
====

.. contents::

What is artificial-architect?
----

Artificial-architect is a Python program for autonomous on-chip network design optimization for a 64-core processor. It uses artificial intelligence techniques including local search and machine learning, as well as a on-chip network simulator. The optimization currently only focuses on the topology of the network, and the optimization goal is to reduce communication latency between network nodes and the power consumption of the network.

Features
----
Here are a few things artificial-architect can do well:

- Network features extraction: extract features including shortest path lengths, clustering coefficient, degree distribution, etc
- Network metrics prediction: predict metrics including communication latency and power consumption based on design knowledge and design features
- Design generation: generate new designs based on existing designs
- User defined optimization objective: the user can trade high performance for low power and vise versa
- Experiments capability: use a network simulator to carry out experiments to evaluate design metrics, extract and record experiments results
- Learning: improve design knowledge based on experiment results using machine learning technique
- Multiple benchmarks for quality evaluation: the quality of designs are evaluated on 8 different parallel computing benchmarks from many different areas such as computer vision, video encoding, financial analytics, animation physics and image processing
- Data analysis and visualization: extract metrics and quality data from simulation record and plot the data
- Parallel optimization: take advantage of multi-core and multi thread processing power of the workstation to boost design speed

Dependencies
----
The following packages are required

- Python 2.7
- matplotlib: http://matplotlib.org/
- simpleai: https://simpleai.readthedocs.org/
- scikit-learn: http://scikit-learn.org/
- networkx: http://networkx.github.io/
- numpy: http://www.numpy.org/
- scipy: http://www.scipy.org/
- pandas: http://pandas.pydata.org/

To install required packages, use the following command::
 sudo pip install matplotlib simpleai scikit-learn networkx numpy scipy pandas

Code
----
To get a copy of the source code, clone the git repository using the the following command::

 git clone https://github.com/yuchenhou/artificial-architect.git

Usage
----
Edit file ``architect.py`` to specify what you want the architect to do.
Activate the architect::

 .architect.py

Authors
----
Yuchen hou <yuchen.hou@wsu.edu>

Domain Background
----

On-chip network is an advanced communication system in modern chip designs. High design quality of on-chip network is always achieved through good trade-offs between many conflicting design features. However, design feature trade-off and design quality analysis become more difficult with the exponential growth of design complexity. Therefore, performing a large number simulations has become the primary method for many design optimization tasks. Also, simulation based design processes are time consuming because simulations are getting more expensive.
