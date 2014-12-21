#!/usr/bin/env python

# modify stdout to flush stream after every call
class Unbuffered(object):
    def __init__(self, stream):
        self.stream = stream
    def write(self, data):
        self.stream.write(data)
        self.stream.flush()
    def __getattr__(self, attr):
        return getattr(self.stream, attr)
import sys
sys.stdout = Unbuffered(sys.stdout)

messages = []
for turn in range(8):
    for i in range(4):
        print 'junk'
    print 'Enter number to change parameter: '
    new_message = sys.stdin.readline()
    print 'Received:', new_message
    messages.append(new_message)
print messages
