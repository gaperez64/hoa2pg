//==============================================================================
//
//  Copyright (c) 2019-
//  Authors:
//  * Guillermo A. Perez <guillermoalberto.perez@uantwerpen.be>
//
//  Based on the cpphoaf parser by Joachim Klein and David Mueller
//
//------------------------------------------------------------------------------
//
//  This file uses the cpphoafparser library,
//      http://automata.tools/hoa/cpphoafparser/
//
//  The cpphoafparser library is free software; you can redistribute it and/or
//  modify it under the terms of the GNU Lesser General Public
//  License as published by the Free Software Foundation; either
//  version 2.1 of the License, or (at your option) any later version.
//
//  The cpphoafparser library is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
//  Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public
//  License along with this library; if not, write to the Free Software
//  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
//
//==============================================================================

#include <algorithm>
#include <queue>
#include <list>
#include <string>
#include <iostream>
#include <fstream>

#include "cpphoafparser/consumer/hoa_consumer_print.hh"
#include "cpphoafparser/consumer/hoa_consumer_null.hh"
#include "cpphoafparser/consumer/hoa_intermediate_trace.hh"
#include "cpphoafparser/consumer/hoa_intermediate_resolve_aliases.hh"
#include "cpphoafparser/parser/hoa_parser.hh"

#include "cuddObj.hh"

#include "SimpleAutomaton.h"
#include "SimpleConsumer.h"
#include "SimpleArena.h"

/** The version */
static const char* version = "1.0";

/** Print version to out */
static void printVersion(std::ostream& out) {
    out << "hoa2pg v" << version;
    out << " (C) Copyright 2019- Guillermo A. Perez" << std::endl;
    out << "Use this tool to translate eHOA files encoding deterministic";
    out << std::endl;
    out << "parity automata into parity games played on graphs.";
    out << std::endl;
}

/** Print usage information, and optionally error message */
static unsigned int usage(const std::string& error = "") {
    if (error != "") {
        printVersion(std::cerr);
        std::cerr << "ERROR: Command-line arguments error: " << error << std::endl;
        std::cerr << "Use argument '--help' to get usage information." << std::endl;
        return 2;
    }

    printVersion(std::cout);
    std::cout << " A single argument is expected: an extended HOA-format";
    std::cout << std::endl;
    std::cout << " file with a deterministic parity automaton" << std::endl;

    return (error != "" ? 2 : 0);
}

int main(int argc, char* argv[]) {
    std::queue<std::string> arguments;
    for (int i=1; i < argc; i++)
        arguments.push(argv[i]);

    if (arguments.size() == 0)
        return usage();

    bool ehoafile_set = false;
    std::string ehoafile;
    unsigned int sindex = 0;
    while (!arguments.empty()) {
        std::string arg(arguments.front());
        arguments.pop();
        if (arg.compare(0, 2, "--") == 0) {
            if (arg == "--help") {
                return usage();
            } else if (arg == "--version") {
                printVersion(std::cout);
                return 0;
            } else {
                return usage("Unexpected option " + arg);
            }
            continue;
        } else {
            if (!ehoafile_set) {
                ehoafile = arg;
                ehoafile_set = true;
            } else {
                return usage("Unexpected argument " + arg);
            }
        }
    }
    if (!ehoafile_set) {
        return usage("Expected a file path with an eHOA file!");
    }

    // Read all files into the automaton data structure
    Cudd mgr(0, 0);
    mgr.AutodynEnable(CUDD_REORDER_SIFT);
    std::vector<SimpleAutomaton> parity_automata;
    std::shared_ptr<std::ifstream> in;
    in.reset(new std::ifstream(ehoafile.c_str()));
    if (!*in) {
        std::cerr << "Error opening file " + ehoafile << std::endl;
        return 1;
    }

    cpphoafparser::HOAConsumer::ptr consumer;
    SimpleAutomaton a;
    consumer.reset(new SimpleConsumer(mgr, a));

    try {
        cpphoafparser::HOAParser::parse(*in, consumer, true);
    } catch (cpphoafparser::HOAParserException& e) {
        std::cerr << e.what() << std::endl;
    } catch (cpphoafparser::HOAConsumerException& e) {
        std::cerr << "Exception: " << e.what() << std::endl;
    }

    assert(a.isComplete());

    // Start creating the generalized parity game
    // Step 1. generate all valuations of inputs
    std::list<BDD> input_vals;

    // we step through input valuations in a "binary counter" fashion
    // so we need a counter to remember the current valuation
    bool val[a.uinputs.size()];
    for (int i = 0; i < a.uinputs.size(); i++)
        val[i] = false;
        
    bool done = false;
    while (!done) {
        BDD valBDD = mgr.bddOne();
        for (int i = 0; i < a.uinputs.size(); i++) {
            BDD varBDD = mgr.bddVar(a.uinputs[i]);
            if (!val[i])
                varBDD = ~varBDD;
            valBDD &= varBDD;
        }
        input_vals.push_back(valBDD);
        // increase the counter
        for (int i = a.uinputs.size() - 1; i >= 0; i--) {
            if (!val[i]) {
                val[i] = true;
                break;
            } else if (i > 0) { // the first digit is never reset
                val[i] = false;
                // and do not break, we need to do carries
            } else {
                done = true;
                break;
            }
        }
    }

    // Step 2. for all states in the automaton and all valuations, create
    // vertices of both players
    unsigned int nindex = 0;
    std::map<unsigned int, unsigned int> state2vertex;
    SimpleArena game;
    for (unsigned int state = 0; state < a.numStates(); state++) {
        if (state2vertex.find(state) == state2vertex.end()) {
            state2vertex[state] = nindex++;
            game.protagonist_vertex.push_back(true);
            game.successors.push_back({});
            game.priorities.push_back(a.priorities[state]);
        }
        // we step through all input valuations now
        for (auto val = input_vals.begin(); val != input_vals.end(); val++) {
            unsigned int nature_vertex = nindex++;
            game.protagonist_vertex.push_back(false);
            game.successors.push_back({});
            // the priorities of the new vertex are copied from the 
            // protagonist vertex
            game.priorities.push_back(a.priorities[state]);
            // connect from state to here
            game.successors[state2vertex[state]].push_back(nature_vertex);
            // connect from here to all successors of state whose transition
            // BDD is compatible with the valuation
            bool atleastone = false;
            for (auto succ = a.successors[state].begin();
                      succ != a.successors[state].end();
                      succ++) {
                // ignore this if the transition is not compatible
                if ((succ->first & *val) == mgr.bddZero())
                    continue;
                // otherwise recover info on the successor
                atleastone = true;
                unsigned int next_state = succ->second;
                if (state2vertex.find(next_state) == state2vertex.end()) {
                    state2vertex[next_state] = nindex++;
                    game.protagonist_vertex.push_back(true);
                    game.successors.push_back({});
                    game.priorities.push_back(a.priorities[next_state]);
                }
                // connect from the intermediate vertex to next state
                game.successors[nature_vertex].push_back(state2vertex[next_state]);
            }
            assert(atleastone);
        }
    }
    assert(game.isComplete());
    assert(game.isReachable());
    game.print();
    return 0;
}
