GLOBAL_FLAGS= -g -W -Wall -Wextra -pedantic # -Werror  # -fopenmp -lgomp # -pthread
# CFLAGS += $(GLOBAL_FLAGS) -std=c99
# CXXFLAGS += $(GLOBAL_FLAGS) --std=c++0x
LDFLAGS:= -lm # -lprofiler -fopenmp
# OBJECTS = main.o CmdLine.o
# port.h ip.h msg.h header.h CmdLine.h CmdLine.cpp main.cpp
all:
	$(CXX) -o simulator.out port.h ip.h msg.h header.h CmdLine.h CmdLine.cpp main.cpp $(LDFLAGS) $(GLOBAL_FLAGS)
.PHONY: clean
clean:
	rm *out