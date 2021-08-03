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
random_functions rf;



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

std::vector<NodeID> random_walk(std::vector<NodeID>& scc,
                                std::vector<int>& comp_num,
                                graph_access& G,
                                std::vector<int> counter_vector,
                                int& walk_length,
                                int& max_removal,
                                bool& random_removal) {       

        int nodes_visited = 1;
        //choose random first node in scc
        NodeID current_node = scc[rf.nextInt(0, scc.size()-1)];
        //increment counter of current visited node
        counter_vector[current_node] += 1;
        //NodeID current_node = scc[random(scc.size()-1)];
        //declare next_node needed in loop below
        NodeID next_node;
        //visit node and randomly choose a neighbor for the next node
        //do that for int walk_length times the size of the scc

        int length;

        if(random_removal == true)
        {
                length = 1;
        }

        else
        {
                length = scc.size()*walk_length;
        }
        

        while(nodes_visited < length)
        {
                //choose random target of node
                next_node = G.getEdgeTarget(G.get_first_edge(current_node)+rf.nextInt(0,G.getNodeDegree(current_node)-1));
                //next_node = G.getEdgeTarget(G.get_first_edge(current_node)+random(G.getNodeDegree(current_node)-1));
                //check if that target is in the current scc
                while(comp_num[current_node] != comp_num[next_node])
                {
                        next_node = G.getEdgeTarget(G.get_first_edge(current_node)+rf.nextInt(0,G.getNodeDegree(current_node)-1));
                        //next_node = G.getEdgeTarget(G.get_first_edge(current_node)+random(G.getNodeDegree(current_node)-1));
                }
                current_node = next_node;
                //increment counter of current visited node
                counter_vector[current_node] += 1;
                nodes_visited += 1;
        }

        std::vector<NodeID> max_nodes;
        //find n max counter nodes

        for(int n = 0; n < max_removal; n++)
        {
                if(n < scc.size()-1)
                {
                        //choose initial node
                        NodeID max_node = scc[0];
                        //std::cout << "max_node1: " << max_node << std::endl;
                        //std::cout << "max_node11: " << counter_vector[max_node] << std::endl;
                        //find node that was visited the most
                        for(int i = 0; i < scc.size(); i++)
                        {
                                //std::cout << "counter_vector[scc[i]]: " << counter_vector[scc[i]] << std::endl;
                                if(counter_vector[scc[i]] > counter_vector[max_node])
                                {
                                        max_node = scc[i];
                                }
                        }
                        //std::cout << "max_node2: " << max_node << std::endl;
                        //std::cout << "max_node22: " << counter_vector[max_node] << std::endl;
                        max_nodes.push_back(max_node);
                        counter_vector[max_node] = -1;
                }
                else
                {
                        break;
                }
                
                
        }

        //get node with max counter

        

        return max_nodes;
}




void fvs_iteration(std::vector<NodeID>& feedback_vertex_set,
                   int& walk_length,
                   int& max_removal,
                   bool& done,
                   std::vector<std::vector<NodeID>>& comp_vector,
                   std::vector<int>& comp_num,
                   std::vector<NodeID>& old_mapping,
                   std::vector<NodeID>& current_mapping,
                   graph_access& Graph,
                   int& exception_removals,
                   bool& random_removal) {

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

        //int graph_half_number = Graph.number_of_nodes()/2;

        counter_vector.resize(Graph.number_of_nodes());

        
        

        for (int comp = 0; comp < comp_vector.size(); comp++)
        {
                if(comp_vector[comp].size() <= 1)
                {
                        //mark node for deletion
                        Graph.setPartitionIndex(comp_vector[comp][0], 1);
                        exception_removals++;
                }
                else
                {
                        //add condition for big sccs
                        /*
                        if(comp_vector[comp].size() > 10000)
                        {
                                walk_length /= 4;
                                if(comp_vector[comp].size() > 100)
                                {
                                        max_removal = 10;
                                }
                        } */

                        std::vector<NodeID> current_max_numbers = random_walk(comp_vector[comp], comp_num, Graph, counter_vector, walk_length, max_removal, random_removal);

                        for (int current_max = 0; current_max < current_max_numbers.size(); current_max++)
                        {
                                //recover original mapping
                                NodeID current_max_recovered = old_mapping[current_mapping[current_max_numbers[current_max]]];
                                //add it to fvs
                                feedback_vertex_set.push_back(current_max_recovered);                        
                                //mark it for removal
                                Graph.setPartitionIndex(current_max_numbers[current_max], 1);
                        }
                        
                }
        }
       

        //if fvs size hasn't changed, we are done
        if(fvs_old_size == feedback_vertex_set.size())
        {
                //std::cout << "done" << std::endl;
                done = true;
                return;
        }
        /*
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
        } */

        /*

        std::cout << std::endl;
        //print out current feedback vertex set

        
        std::cout << "fvs: ";

        for(int i = 0; i < feedback_vertex_set.size(); i++)
        {
                std::cout << feedback_vertex_set[i]+1 << " ";
        }
        std::cout << "max_removal: " << max_removal << std::endl;

        
        std::cout << std::endl;
        std::cout << std::endl;

        std::cout << "walk_length: " << walk_length << std::endl;
        std::cout << std::endl;
        std::cout << "comp: " << comp_vector.size() << std::endl;
        std::cout << std::endl;
        std::cout << "graphnumber: " << Graph.number_of_nodes()/2 << std::endl;
        std::cout << std::endl;

        std::cout << "----------------------------------------------------------" << std::endl;

        std::cout << std::endl;

        */

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
        //temp_graph.copy(Graph);
        //Graph = std::move(temp_graph);
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
                        int& walk_length,
                        int& max_removal,
                        int& iterations,
                        int& exception_removals,
                        bool& random_removal) {

        //monitor progress
        bool done = false;

        //create original mapping
        std::vector<NodeID> old_mapping;

        for(int i = 0; i < Graph.number_of_nodes(); i++)
        {
                old_mapping.push_back(i);
        }
        //create new, current mapping
        std::vector<NodeID> current_mapping = old_mapping;

        while (!done)
        {
                /*
                std::cout << "Iteration: " << iterations << std::endl;
                std::cout << std::endl;
                std::cout << "graph size (number of nodes): " << Graph.number_of_nodes() << std::endl;
                std::cout << std::endl;
                std::cout << "walk_length: " << walk_length << std::endl;
                std::cout << std::endl;
                */
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
                
               	/* 
                int max_size = 0;
                std::cout << "comp_count: " << comp_count << std::endl;
                std::cout << "scc_vector.size(): " << scc_vector.size() << std::endl;
                std::cout << Graph.number_of_nodes() << std::endl;
                int size_one = 0;
                for(int i = 0; i < scc_vector.size(); i++)
                {
                        if(scc_vector[i].size() == 1)
                        {
                                size_one += 1;
                        }
                }

                std::cout << "size_one: " << size_one << std::endl;
                
                
                int max_size_index = 0;

                for(int i = 0; i < scc_vector.size(); i++)
                {
                        if(scc_vector[i].size() != 1)
                        {
                                //std::cout << "scc_vector[i].size(): " << scc_vector[i].size() << std::endl;
                        }
                        
                        if(scc_vector[i].size() > max_size)
                        {
                                //std::cout << "max_size_temp: " << max_size << std::endl;
                                max_size = scc_vector[i].size();
                                max_size_index = i;
                        }
                }
                std::cout << "max_size: " << max_size << std::endl;
                
                return; 
                */
                /*
                int max_edges;
                for(int j = 0; j < scc_vector[max_size_index].size(); j++)
                {
                        //std::cout << scc_vector[max_size_index][0] << std::endl;
                        //std::cout << scc_vector[max_size_index][j] << std::endl;

                        for(int x = 0; x < Graph.getNodeDegree(scc_vector[max_size_index][j])-1.; x++)
                        {
                                std::cout << Graph.getNodeDegree(scc_vector[max_size_index][j])-1 << std::endl;
                                std::cout << scc_vector[max_size_index][j] << std::endl;
                                std::cout << scc_by_node(scc_vector[max_size_index][j]) << std::endl;
                                if(scc_by_node(Graph.getEdgeTarget(Graph.get_first_edge(scc_vector[max_size_index][j])+x))==scc_by_node(scc_vector[max_size_index][j]))
                                {
                                        max_edges += 1;
                                }
                        }
                } 
                
                std::cout << 'max_edges: ' << max_edges << std::endl; */

                //G.getNodeDegree(current_node)-1
                //G.getEdgeTarget(G.get_first_edge(current_node)

                //return;
                //get nodes we want to remove and add to fvs for the current iteration
                //then assign the current graph to the newly created graph, which
                //doesn't hold the nodes we marked for deletion anymore
                fvs_iteration(feedback_vertex_set, walk_length, max_removal, done, scc_vector, scc_by_node, old_mapping, current_mapping, Graph, exception_removals, random_removal);
                iterations++;               
        }

        return feedback_vertex_set;
}

void solution_checker(graph_access& Graph,
                      std::vector<NodeID>& feedback_vertex_set,
                      std::vector<int>& result) {

        //std::cout << "Check if calculated solution is indeed a feedback vertex set" << std::endl;
        //std::cout << std::endl;
        //mark fvs node for deletion
        for(int node = 0; node < feedback_vertex_set.size(); node++)
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

        result[0] = Graph2.number_of_nodes();
        result[1] = comp_count;

        /*
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
        */

}

#include <ctime>
#include <chrono>
#include <iostream>
#include <fstream>
#include <limits>
#include<sys/stat.h>
#include<sys/types.h>
void aggregate_data(graph_access& Graph, 
                    int& walk_length, 
                    int& max_removal, 
                    int& runs, 
                    bool& random_removal, 
                    std::string graph_filename,
		    int& user_seed) {

        NodeID number_of_nodes = Graph.number_of_nodes();
        EdgeID number_of_edges = Graph.number_of_edges();

        
        auto start_time = std::chrono::system_clock::now();
        auto end_time = std::chrono::system_clock::now();

        std::vector<std::vector<int>> data;

	std::string path = "/results/fvs/" + graph_filename + "_" + "wl" + std::to_string(walk_length) + "_" + "mr" + std::to_string(max_removal) + "/";

        std::ofstream file;
        std::string filename;
        filename = graph_filename + "_" + "wl" + std::to_string(walk_length) + "_" + "mr" + std::to_string(max_removal) + "_" + "seed" + std::to_string(user_seed);


        if(random_removal == true)
        {
                filename += "_random";
        }

	file.open (filename + ".csv");


	file << "graph name,#nodes,#edges,seed,walk_length,max_removal,random_removal,iterations,time(ms),fvs_size,nodes in graph without fvs,#scc without fvs,exception removals,calculated fvs,\n";
        file.flush();
        for(int i = 0; i < runs; i++)
        {
                graph_access G;
                Graph.copy(G);
                //copy Graph for later solution checking
                graph_access G2;
                //G.copy(G2);
                G.copy(G2);
                std::vector<NodeID> fvs1;
                int iterations = 0;
                int exception_removals = 0;
                int seed = user_seed;
		rf.setSeed(seed);
                start_time = std::chrono::system_clock::now();
                fvs1 = fvs(G, fvs1, walk_length, max_removal, iterations, exception_removals, random_removal);
                end_time = std::chrono::system_clock::now();
                int fvs_size = fvs1.size();
                int time = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
                std::vector<int> result(2);
                solution_checker(G2, fvs1, result);

                file << graph_filename << "," << number_of_nodes << "," << number_of_edges << "," << seed << "," << walk_length << "," << max_removal << "," << random_removal << "," << iterations << "," << time << "," << fvs_size << "," << result[0] << "," << result[1] << "," << exception_removals << ",\n";
                file.flush();
		file.clear();
		file.close();
		//std::cout << "i: " << i << std::endl;
                std::cout << "time: " << time << std::endl;
		std::cout << "fvs size: " << fvs1.size() << std::endl;

		std::cout << "Statistics .csv file written" << std::endl;
	        std::cout << std::endl;


		std::ofstream file_fvs;
		std::string fvs_filename;
		fvs_filename = graph_filename + "_" + "wl" + std::to_string(walk_length) + "_" + "mr" + std::to_string(max_removal) + "_" + "seed" + std::to_string(user_seed) + "_" + "fvs";
		

		if(random_removal == true)
	        {
               		fvs_filename += "_random";
       		}

		//file.open (fvs_filename + ".txt");
		file_fvs.open (fvs_filename + ".txt");

                
                for (int i = 0; i < fvs1.size(); i++)
                {
                        file_fvs << fvs1[i] << " ";
			file_fvs.flush();
                }
		//file.clear();
		//file.close();

		file_fvs.clear();
		file_fvs.close();


		std::cout << std::endl;
		std::cout << "fvs.txt file written" << std::endl;
		std::cout << std::endl;

                //data[5].push_back(iterations, time, fvs_size, result[0], result[1], result[0] == result[1]);
                /*
                data[0].push_back(iterations);
                data[1].push_back(time);
                data[2].push_back(fvs_size);
                data[3].push_back(result[0]);
                data[4].push_back(result[1]);
                data[5].push_back(exception_removals);
                */
        }


        //min and max fvs
	//file.close();

	std::cout << "-------------------------------------------" << std::endl;

}


void statistics (std::vector<int> data) {
        
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


        int walk_length = partition_config.walk_length;
        int max_removal = partition_config.max_removal;
	int user_seed = partition_config.seed;
        std::cout << "walk_length: " << walk_length << std::endl;
        std::cout << "max_removal: " << max_removal << std::endl;
	std::cout << "user_seed: " << user_seed << std::endl;
        bool random_removal = partition_config.random_removal;

        std::cout << "random removal: " << random_removal << std::endl;
        int runs  = 1;
        aggregate_data(G, walk_length, max_removal, runs, random_removal, graph_filename,user_seed);

        /*
        //create fvs vector
        std::vector<NodeID> fvs1;
        //copy Grpah for later solution checking
        graph_access G2;
        //G.copy(G2);
        G.copy(G2);
        int walk_length = partition_config.walk_length;
        int max_removal = 1;

        //run fvs function
        fvs(G, fvs1, walk_length, max_removal);

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
        //solution_checker(G2, fvs1);

        */
        
        



        

}
