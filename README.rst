architect
=========

.. contents::

What is Architect?
----
Architect is a Python program for autonomous on-chip network optimization for a 64-core processor. It uses artificial intelligence techniques including local search and machine learning.

Motivation:
---

The problem this project focuses on is on-chip network design automation. On-chip network has become increasingly prevalent as the communication system in modern chip designs. A key in a good on-chip network is usually a good trade-off between many conflicting design features. An architect might be able to tell how good every feature of the design is, but even the most experienced architects can have only a vague idea about the best trade-off point. Along with the exponential growth of design complexity, design quality analysis and design feature trade-off become more difficult. Therefore, performing a large number simulations has become the primary method for many design optimization tasks. Although we have sophisticated simulators to accurately assess design qualities, design processes still heavily depend on intellectual engagement of human. Also, simulation based design processes are time consuming because simulations are getting more expensive. Computer aided design tools we have now mostly deal with only low level design optimization, but not high level design optimization. This leads to a well known issue in chip design - productivity gap: design complexity keeps increasing rapidly, but designer productivity is lagged behind.
