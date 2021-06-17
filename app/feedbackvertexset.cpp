/******************************************************************************
 * kaffpa.cpp 
 * *
 * Source of KaHIP -- Karlsruhe High Quality Partitioning.
 * Christian Schulz <christian.schulz.phone@gmail.com>
 *****************************************************************************/

#include <argtable3.h>
#include <iostream>
#include <math.h>
#include <regex.h>
#include <sstream>
#include <stdio.h>
#include <string.h>
#include <algorithm>
#include <vector>

#include "balance_configuration.h"
#include "data_structure/graph_access.h"
#include "data_structure/matrix/normal_matrix.h"
#include "data_structure/matrix/online_distance_matrix.h"
#include "graph_io.h"
#include "macros_assertions.h"
#include "mapping/mapping_algorithms.h"
#include "mmap_graph_io.h"
#include "parse_parameters.h"
#include "partition/graph_partitioner.h"
#include "partition/partition_config.h"
#include "partition/uncoarsening/refinement/cycle_improvements/cycle_refinement.h"
#include "quality_metrics.h"
#include "random_functions.h"
#include "timer.h"
#include "algorithms/strongly_connected_components.h"
#include "lib/tools/graph_extractor.h"
#include "algorithms/cycle_search.h"

#include <random>

//init random 
std::random_device dev;
std::mt19937 rng(dev());

NodeID random(int range){

//line 30 random function

//short code fragment for random selection
//taken from: https://stackoverflow.com/questions/13445688/how-to-generate-a-random-number-in-c
//(Cornstalks' answer)    
std::uniform_int_distribution<std::mt19937::result_type> distn(0,range); // distribution in range [0, range]
return distn(rng);
//std::cout << distn(rng) << std::endl;
}

std::vector<std::vector<NodeID>> build_scc_vector(std::vector<int>& comp_num, int comp_count)
{
        //build comp vector where all sccs will be stored in
        std::vector<std::vector<NodeID>> comp_vector;
        comp_vector.resize(comp_count);

        //loop over comp_num vector and push each node into associated component vector
        for(NodeID node = 0; node < comp_num.size(); node++)
        {
                comp_vector[comp_num[node]].push_back(node);
        }

        return comp_vector;
}

NodeID random_walk(std::vector<NodeID>& scc,
                   std::vector<int>& comp_num,
                   graph_access& G,
                   std::vector<int>& counter_vector,
                   int& walk_length) {       

        int nodes_visited = 1;

        //choose random first node in scc
        NodeID current_node = scc[random(scc.size()-1)];
        //declare next_node needed in loop below
        NodeID next_node;
        //visit node and randomly choose a neighbor for the next node
        //do that for int walk_length times the size of the scc
        while(nodes_visited < scc.size()*walk_length)
        {
                //increment counter of current visited node
                counter_vector[current_node] += 1;
                //choose random target of node
                next_node = G.getEdgeTarget(G.get_first_edge(current_node)+random(G.getNodeDegree(current_node)-1));
                //check if that target is in the current scc
                while(comp_num[current_node] != comp_num[next_node])
                {
                        next_node = G.getEdgeTarget(G.get_first_edge(current_node)+random(G.getNodeDegree(current_node)-1));
                }
                current_node = next_node;
                nodes_visited += 1;
        }
        //get node with max counter

        //choose initial node
        NodeID max_node = scc[0];
        //find node that was visited the most
        for(int i = 0; i < scc.size(); i++)
        {
                if(counter_vector[scc[i]] > counter_vector[max_node])
                {
                        max_node = scc[i];
                }
        }

        return max_node;
}


void fvs_iteration(std::vector<NodeID>& feedback_vertex_set,
                   int& walk_length,
                   bool& done,
                   std::vector<std::vector<NodeID>>& comp_vector,
                   std::vector<int>& comp_num,
                   std::vector<NodeID>& old_mapping,
                   std::vector<NodeID>& current_mapping,
                   graph_access& Graph) {

        //monitor fvs size change, if it doesn't change, we are done
        NodeID fvs_old_size = feedback_vertex_set.size();
        //create current vector of nodes we want to remove/collect in the fvs
        std::vector<NodeID> current_nodes;
        //create counter vector for nodes we want to remove/collect in the fvs
        std::vector<int> counter_vector;

        /*
        std::cout << "mapping order " << std::endl;
        for(int i = 0; i < current_mapping.size(); i++)
        {
                std::cout << "index " << i << " mapping index: " << current_mapping[i];
                std::cout << std::endl;
        }
        */


        counter_vector.resize(Graph.number_of_nodes());

        for (int comp = 0; comp < comp_vector.size(); comp++)
        {
                if(comp_vector[comp].size() <= 1)
                {
                        //mark node for deletion
                        Graph.setPartitionIndex(comp_vector[comp][0], 1);
                }
                else
                {
                        NodeID current_max = random_walk(comp_vector[comp], comp_num, Graph, counter_vector, walk_length);
                        //recover original mapping
                        NodeID current_max_recovered = old_mapping[current_mapping[current_max]];
                        //add it to fvs
                        feedback_vertex_set.push_back(current_max_recovered);                        
                        //mark it for removal
                        Graph.setPartitionIndex(current_max, 1);
                }
        }

        //if fvs size hasn't changed, we are done
        if(fvs_old_size == feedback_vertex_set.size())
        {
                std::cout << "done" << std::endl;
                done = true;
                return;
        }

        //print out counter vector with # of how often each node was visited
        for (int comp = 0; comp < comp_vector.size(); comp++)
        {
                std::cout << "Component: " << comp +1 << std::endl;
                for(NodeID node = 0; node < comp_vector[comp].size(); node++)
                {
                        std::cout << "node: " << comp_vector[comp][node]
                        << ", recovered node: "<< old_mapping[current_mapping[comp_vector[comp][node]]]+1
                        << ", counter " << counter_vector[comp_vector[comp][node]]
                        << ", Partition " << Graph.getPartitionIndex(comp_vector[comp][node]) << std::endl;
                }
        }


        std::cout << std::endl;
        //print out current feedback vertex set
        std::cout << "fvs: ";

        for(int i = 0; i < feedback_vertex_set.size(); i++)
        {
                std::cout << feedback_vertex_set[i]+1 << " ";
        }

        std::cout << std::endl;
        std::cout << std::endl;
        std::cout << "----------------------------------------------------------" << std::endl;

        std::cout << std::endl;
        //create graph_extractor object needed for extraction
        graph_extractor ge;
        //create graph_access object needed for extraction
        graph_access temp_graph;
        //create and order mapping for correct node recovery by new indices
        for(int i = 0; i < current_mapping.size(); i++)
        {
                current_mapping[i] = old_mapping[current_mapping[i]];
        }
        old_mapping = current_mapping;
        std::vector<NodeID> new_mapping;
        //extract marked nodes
        ge.extract_block(Graph, temp_graph, 0, new_mapping);
        //assign new graph via deep copy
        temp_graph.copy(Graph);
        //set partition indices to 0
        forall_nodes(Graph, node) {
                Graph.setPartitionIndex(node,0);
        } endfor
        //update current mapping
        current_mapping = new_mapping;
}

std::vector<NodeID> fvs(graph_access& Graph, 
                        std::vector<NodeID>& feedback_vertex_set,
                        int& walk_length) {

        //monitor progress
        bool done = false;

        //create original mapping
        std::vector<NodeID> old_mapping;

        for(int i = 0; i < Graph.number_of_nodes(); i++)
        {
                old_mapping.push_back(i);
        }
        int iter = 0;
        //create new, current mapping
        std::vector<NodeID> current_mapping = old_mapping;

        while (!done)
        {
                std::cout << "Iteration: " << iter << std::endl;
                std::cout << std::endl;
                std::cout << "graph size (number of nodes): " << Graph.number_of_nodes() << std::endl;
                std::cout << std::endl;
                //create scc by node index vector
                std::vector<int> scc_by_node;
                //adjust its size to number of nodes
                scc_by_node.resize(Graph.number_of_nodes());
                //create KaHIPs scc object
                strongly_connected_components scc; 
                //comp count = number of scc in the graph
                int comp_count = scc.strong_components(Graph, scc_by_node);
                //create vector of vectors, which stores every scc with its nodes
                std::vector<std::vector<NodeID>> scc_vector = build_scc_vector(scc_by_node, comp_count);
                //get nodes we want to remove and add to fvs for the current iteration
                //then assign the current graph to the newly created graph, which
                //doesn't hold the nodes we marked for deletion anymore
                fvs_iteration(feedback_vertex_set, walk_length, done, scc_vector, scc_by_node, old_mapping, current_mapping, Graph);
                iter++;               
        }

        return feedback_vertex_set;
}

void solution_checker(graph_access& Graph,
                      std::vector<NodeID>& feedback_vertex_set) {

        std::cout << "Check if calculated solution is indeed a feedback vertex set" << std::endl;
        std::cout << std::endl;
        //mark fvs node for deletion
        for(int node; node < feedback_vertex_set.size(); node++)
        {       
                Graph.setPartitionIndex(feedback_vertex_set[node], 1);
        }

        //create graph without the fvs
        graph_access Graph2;
        std::vector<NodeID> mapping;
        //create graph_extractor object needed for extraction
        graph_extractor ge;
        //extract marked nodes
        ge.extract_block(Graph, Graph2, 0, mapping);
        //check for scc
        //create scc by node index vector
        std::vector<int> scc_by_node;
        //adjust its size to number of nodes
        scc_by_node.resize(Graph2.number_of_nodes());
        //create KaHIPs scc object
        strongly_connected_components scc; 
        //comp count = number of scc in the graph
        int comp_count = scc.strong_components(Graph2, scc_by_node);

        if (Graph2.number_of_nodes() != comp_count)
        {
                std::cout << "Calculated solution is NOT a feedback vertex set. " << std::endl; 
                std::cout << "Number of nodes in the graph without calculated feedback vertex set is: " << std::endl;
                std::cout << Graph2.number_of_nodes() << std::endl;
                std::cout << "Where as calculated number of strongly connected components in that Graph is: " << std::endl;
                std::cout << comp_count << std::endl;
        }
        else
        {
                std::cout << "Calculated solution IS a feedback vertex set. " << std::endl;
                std::cout << "Number of nodes in the graph without calculated feedback vertex set is: " << std::endl;
                std::cout << Graph2.number_of_nodes() << std::endl;
                std::cout << "Where as calculated number of strongly connected components in that Graph is: " << std::endl;
                std::cout << comp_count << std::endl;
        }

}



int main(int argn, char **argv) {

        PartitionConfig partition_config;
        std::string graph_filename;

        bool is_graph_weighted = false;
        bool suppress_output   = false;
        bool recursive         = false;

        int ret_code = parse_parameters(argn, argv, 
                        partition_config, 
                        graph_filename, 
                        is_graph_weighted, 
                        suppress_output, recursive); 

        if(ret_code) {
                return 0;
        }
        
        partition_config.LogDump(stdout);
        graph_access G;     

        timer t;
        if (partition_config.use_mmap_io) {
                kahip::mmap_io::graph_from_metis_file(G, graph_filename);
        } else {
                graph_io::readGraphWeighted(G, graph_filename);
        }
        

        /*
        forall_nodes(G, node) {
                forall_out_edges(G, e, node) {
                        NodeID target = G.getEdgeTarget(e);
                        std::cout <<  "node " <<  node+1 <<  " target " <<  target+1 << std::endl;
                } endfor
        } endfor
        */

        //create fvs vector
        std::vector<NodeID> fvs1;
        //copy Grpah for later solution checking
        graph_access G2;
        G.copy(G2);
        int walk_length = partition_config.walk_length;

        //run fvs function
        fvs(G, fvs1, walk_length);

        std::cout << std::endl;
        std::cout << "----------------------------------------------------------" << std::endl;
        std::cout << std::endl;
        std::cout << "fvs size: " << fvs1.size() << std::endl;

        std::cout << "fvs: " << std::endl;

        for(int i = 0; i < fvs1.size(); i++)
        {
                std::cout << fvs1[i]+1 << " ";
        }

        std::cout << std::endl;
        std::cout << "----------------------------------------------------------" << std::endl;
        std::cout << std::endl;
        //check calculated solution
        solution_checker(G2, fvs1);
        
        



        

}
