/**
 * Efficient Greedy Lottery Wheel Generator
 *auto_ptr
 * Author: Tyler McHenry <tyler@nerdland.net>
 *
 * For a more thorough description of the design and implementation of this
 * generator than can be provided in the in-line comments (with pretty diagrams
 * and everything!) please see "The Lottery Problem", a series of articles on
 * Nerdland: http://nerdland.net/the-lottery-problem/
 *
 * Licensing:
 *
 *   This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Some general notes:
 *
 * - This is NOT an optimal wheel generator. It generates pretty good wheels,
 *   and it does so relatively quickly (given the problem complexity) but it
 *   does NOT reliably produce optimal results. This program is part of a
 *   continuing effort to produce such an optimal generator, but it does not yet
 *   achieve this goal.
 *
 * - This code has been tested only with relatively recent versions of g++, and
 *   not with any other compiler, or on Windows. This should in theory compile
 *   on any system that implements the C++ standard and which provides the POSIX
 *   sys/types.h header. Memory usage may increase on non-gcc builds due to the
 *   unavailability of gcc's struct-packing extensions.
 *
 * - This code makes use of the unordered_map container from Technical Report 1
 *   of the C++0x draft standard. If your compiler does not support this, you
 *   can safely replace all uses of std::tr1::unordered_map with std::map, at
 *   the expense of decreased performance (due to unnecessary balancing of the
 *   red-black tree that underlies std::map).
 *
 * - This code is optimized for performance, sometimes at the expense of
 *   readability. Since large data structures are dealt with when generating
 *   wheels for larger lotteries, many functions return their results through
 *   output parameters rather than as normal return values (to avoid copying).
 *
 * - The output of this program is a bit verbose, since for some inputs it may
 *   run for a very long time and it would be useful to know how far along it
 *   is. When building the problem graph, it outputs a . each time it finishes
 *   creating one thousand nodes. When generating the wheel, it outputs a . each
 *   time it covers 100 new tickets, and also outputs the percentage complete
 *   each time it increases by at least 1%. Percentage completeness is measured
 *   as the number of tickets covered out of all possible tickets. Note that the
 *   rate at which tickets are covered will increase as the computation
 *   progresses.
 *
 * Last Modified: 11 July 2009
 *
 **/

#include <cmath>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <stack>
#include <string>
#include <sstream>
#include <fstream>
#include <memory>
#include <unordered_map>
#include <boost/functional/hash.hpp>
#include <sys/types.h>
#include "testeNovagen.h"
#include <random>
#include <chrono>
#include <time.h>
#include <algorithm>
#include <boost/dynamic_bitset.hpp>

using std::cout;
using std::cerr;
using std::cin;
using std::endl;
using std::string;
using std::stringstream;
using std::ofstream;
using std::vector;
using std::stack;
using std::unordered_map;
using std::abs;
using std::unique_ptr;

// Problem parameters - used all over the place, so actually cleaner as
// unit-scope globals than as parameters to every function

static size_t qtd_dezenas_jogo;   ///< numeros da loteriaRange size (r), e.g. a total de dezenas no sorteio exemplo mega-sena 60 dezenas.
static size_t qtd_dezenas_sorteio;  ///< Ticket size (t), quantidade de dezenas que vao ser sorteadas exemplo mega-sena 6
static size_t qtd_dez_garante_acertos;  ///< quantidade de dezenas de garantia de acertos
static size_t menorAposta; ///< busca para aceitar o menor numero de combincao
  /** < Match size (m), quantidade de dezenas que queremos garantir de acertos no jogo
exemplo mega-sena sorteia 6 dezenas queremos garantir 5 ent�o a garantia sera 5 */
//unordered_map<uint32_t, uint32_t> tentativa_idx_map;
  //criado para não gerar roda novamente caso for fazer mais teste de busca
  vector<TicketNode> ticket_nodes_cp;
  vector<MatchNode> garantias_nodes_cp;
/** Prints a ticket (or a match, which is like a partial ticket) in a nice, human readable format */
static string ticketToString(boost::dynamic_bitset<>& bs){
	std::string ap = std::string("");
	//char buffer [80];
	std::stringstream sstr;

	for (int var = 0; var < bs.size(); ++var) {
		   if(bs[var]){
				if (sstr.str().length() > 0)  sstr << ";";
                sstr << var+1;
		    }
	}
	return sstr.str();
}
static uint64_t comb(uint64_t n, uint64_t k)
{
  uint64_t b[n+1];

  b[0] = 1;

  for (uint64_t i = 1; i <= n; ++i) {
    b[i] = 1;
    for (uint64_t j = i - 1; j > 0; --j) {
      b[j] += b[j-1];
    }
  }

  return b[k];
}
static  uint64_t computeStartingCoverage(uint64_t range, uint64_t ticket_size,
                               size_t match_size)
{ 
  uint64_t starting_coverage = 0;
  
  for (uint64_t k = match_size; k < ticket_size; ++k) {
    starting_coverage += comb(ticket_size, k) *
      comb(range - ticket_size, ticket_size - k);
  }

  return starting_coverage;
}
static boost::dynamic_bitset<> convertNumBitset(std::vector<int> numeros, int max){

	boost::dynamic_bitset<> convertido(max);
	for ( int var = 0; var < numeros.size(); ++var){
		convertido.set(numeros[var]-1);
	}
	return convertido;
}
static std::vector<int> convertBitsetNum(boost::dynamic_bitset<> numerosbit){
	std::vector<int> bit_vector;
	std::size_t pos = numerosbit.find_first();
	while (pos != boost::dynamic_bitset<>::npos) {
		bit_vector.push_back(pos+1);
		pos = numerosbit.find_next(pos);
	}
	return bit_vector;
}
/**
 * Builds the first part of the problem graph by creating a MatchNode struct for
 * each match in the todas_garantias vector.
 **/


static void geraCombinacoes(std::vector<int> entrada, int numero, std::vector<std::vector<int>>& comb){

		int N[numero] ;
		int k[numero];
		for (unsigned int var = 0; var < numero; ++var) {
			k[var]=0;
			N[var]=var;
		}
		int d=0;
		std::vector<int> combination;
		if(numero <=entrada.size()){
			std::vector<int> combination;
			for (unsigned int j = 0; j < numero; j++) {
				//cobminação gerada
				//cout<<entrada[N[j]]<<"";
				combination.push_back(entrada[N[j]]);
			}
			//std::cout<<std::endl;
			comb.push_back(combination);
		//totalCombinacoes.push_back(bs);
		}

	if(numero <entrada.size()){


			for (int b = numero-1; b >=0; b--) {
				k[b] =entrada.size()-d;
				d++;

			}


		bool verdade=true;

		while(verdade){

			N[numero-1]++;

			if(N[numero-1]<k[numero-1]){

				combination.clear();
				for (unsigned int j = 0; j < numero; j++) {
					//combinacoes geradas
					combination.push_back(entrada[N[j]]);
					//cout<<(entrada[N[j]])<<" ";

				}
				comb.push_back(combination);

				//System.out.println(Arrays.toString(N));
				if(N[0]==k[0]-1)verdade=false;

			}else{

				for (int l = numero-1; l >=0 ; l--) {

					if(N[l]==k[l]){
						N[l-1]+=1;
						N[l]=N[l-1];

					}
				}
			}


		}
		//System.out.println("total de combina��es "+contarComb);
	}
}


static void generateCombinations(boost::dynamic_bitset<>& combination, int index, int remaining, std::vector<boost::dynamic_bitset<>>& comb)
{
	if (remaining == 0)
	{
		
		comb.push_back(combination);
		return;
	}

	if (index >= combination.size())
	{
		return;
	}

	// Select the current number
	combination[index] = true;
	generateCombinations(combination, index + 1, remaining - 1, comb);

	// Do not select the current number
	combination[index] = false;
	generateCombinations(combination, index + 1, remaining, comb);
}
static void convertMatchesToMatchNodes(vector<boost::dynamic_bitset<>>& todas_garantias,
                                       vector<MatchNode>& garantias_nodes,
                                       unordered_map<boost::dynamic_bitset<>, uint64_t>& garantias_idx_map)
{
  size_t ticket_idx_reserve_sz = comb(qtd_dezenas_jogo - qtd_dez_garante_acertos, qtd_dezenas_sorteio - qtd_dez_garante_acertos);                  //(17     -              14 ) =3             15 -
  //    14 = 1
  uint64_t garantias_idx = 0;

  garantias_nodes.resize(todas_garantias.size());

  for (vector<boost::dynamic_bitset<>>::const_iterator m = todas_garantias.begin();
       m != todas_garantias.end(); ++garantias_idx, ++m)
    {
      garantias_nodes[garantias_idx].ticket_indexes.reserve(ticket_idx_reserve_sz);
      garantias_idx_map[(*m)] = garantias_idx;

    //   if (garantias_idx % 1000 == 0) {
    //     cout << ".";
    //     cout.flush();
    //   }
    }
}


/**
 * Builds the second part of the problem graph by creating a TicketNode struct
 * for each ticket in the all_tickets vector. Then, it determines which matches
 * this ticket contains and "connects" the TicketNode to each of these match
 * nodes (by inserting an index reference to the ticket node in the match node
 * and vice-versa.
 **/
static void convertTicketsToTicketNodesModificado(std::vector<boost::dynamic_bitset<>>& all_tickets,
std::vector<TicketNode>& ticket_nodes, std::vector<MatchNode>& garantias_nodes)
{
	size_t ticket_cover_initial_size = computeStartingCoverage(qtd_dezenas_jogo, qtd_dezenas_sorteio, qtd_dez_garante_acertos);
	uint64_t ticket_idx = 0;


	ticket_nodes.resize(all_tickets.size());


	for (std::vector<boost::dynamic_bitset<>>::const_iterator t = all_tickets.begin();
		t != all_tickets.end(); ++ticket_idx, ++t)
	{

		ticket_nodes[ticket_idx].is_covered = 0;
		ticket_nodes[ticket_idx].remaining_coverage = ticket_cover_initial_size;
		uint64_t garantias_idx = 0;

		// vector<vector<int>> matches_for_ticket;
		// vector<int> entrada= convertBitsetNum(*t);
		//geraCombinacoes(entrada, qtd_dez_garante_acertos, matches_for_ticket);

		for (uint64_t idx=0;idx<all_tickets.size(); ++idx)
			{
				//boost::dynamic_bitset<> numBitset = convertNumBitset(combMenor[i],qtd_dezenas_jogo);
				//uint64_t idxGaratia = garantias_idx_map.find(numBitset)->second;
				
				if((all_tickets[idx]&(*t)).count() == qtd_dez_garante_acertos){
					ticket_nodes[ticket_idx].match_indexes.push_back(idx);
					if(ticket_cover_initial_size==	ticket_nodes[ticket_idx].match_indexes.size())break;
				}
							
			}
		// for (vector<vector<int>>::const_iterator m = matches_for_ticket.begin();
		// 	m != matches_for_ticket.end();++garantias_idx, ++m)
		// {

		// 		uint64_t garantias_idx = (garantias_idx_map.find(convertNumBitset((*m),(*t).size())))->second;
		// 		//ticket_nodes[ticket_idx].match_indexes.push_back(garantias_idx);
		// 		garantias_nodes[garantias_idx].ticket_indexes.push_back(ticket_idx);
		// 	//std::cout<<i<<"\n";
		// 	// system("pause");

		// }


	}
	if (ticket_idx % 1000 == 0) {
		cout << ".";
		cout.flush();
	}
}

/**
 * Builds the problem graph - converts ticket and match descriptions to
 * interconnected ticket and match nodes, and in the process loses the
 * description information.
 **/
static void generateNodes(std::vector<boost::dynamic_bitset<>>& all_tickets,
                          std::vector<boost::dynamic_bitset<>>& todas_garantias,
                          vector<TicketNode>& ticket_nodes,
                          vector<MatchNode>& garantias_nodes)
{
//  unordered_map<boost::dynamic_bitset<>, uint64_t> garantias_idx_map(todas_garantias.size());

//   cout << "Indexando todas garantias...";
//   cout.flush();
//   convertMatchesToMatchNodes(todas_garantias, garantias_nodes, garantias_idx_map);
//   todas_garantias.clear();
//   todas_garantias.reserve(0);
//   cout << "done." << endl;

  cout << "Indexando todos tickets...";
  cout.flush();
  convertTicketsToTicketNodesModificado(all_tickets, ticket_nodes,garantias_nodes);
//   all_tickets.clear();
//   all_tickets.reserve(0);

   cout << "done." << endl;
}


/**
 * This is the part that makes this generator fast. Here we do an efficient
 * depth-first walk of the problem graph and update the coverage potentials of
 * all tickets based on the ticket that we just selected for the wheel. Because
 * the coverage potentials are kept accurate, the selection of the next ticket
 * can always be done in O(n) time.
 **/
static void updateSimpleCovered(std::vector<boost::dynamic_bitset<>>& all_tickets,std::vector<TicketNode>& ticket_nodes,uint64_t start_index,uint64_t acertoGarantia,vector<uint64_t> &idx_remaining){

	
	for (uint64_t l:ticket_nodes[start_index].match_indexes){
		ticket_nodes[l].is_covered=true;
		ticket_nodes[l].remaining_coverage=0;
		
		idx_remaining.erase(std::remove(idx_remaining.begin(), idx_remaining.end(), l)	,idx_remaining.end());
	
	}
	
	for (uint64_t i = 0; i < ticket_nodes.size(); i++){
		if (ticket_nodes[i].is_covered)continue;
		// for (uint64_t l:ticket_nodes[i].match_indexes){
		// 		if (start_index==l){
		// 			system("pause");
		// 		}
		// 	}
		unsigned potencialCobre=0;
		for (size_t j : idx_remaining)
		{
			//if (ticket_nodes[j].is_covered)continue;
			if(( all_tickets[i] & all_tickets[j]).count()==acertoGarantia){
				potencialCobre++;
			}
			
	
		}
		
		
		ticket_nodes[i].remaining_coverage=potencialCobre;
		//cout<<potencialCobre;
		//system("pause");

	}
}

static void updateStartCovered(std::vector<boost::dynamic_bitset<>>& all_tickets,std::vector<TicketNode>& ticket_nodes,uint64_t start_index,uint64_t acertoGarantia){

	for (uint64_t i = 0; i < ticket_nodes.size(); i++){
		
		unsigned potencialCobre=0;
		for (size_t j = 0;j < ticket_nodes.size(); j++)
		{
			//if (ticket_nodes[j].is_covered)continue;
			if(( all_tickets[i] & all_tickets[j]).count()==acertoGarantia){
				potencialCobre++;
			}
				
		}
				
		ticket_nodes[i].remaining_coverage=potencialCobre;
	
	}
}

static void updatePotentials(vector<TicketNode>& ticket_nodes,
                             vector<MatchNode>& garantias_nodes,
                             uint64_t start_ticket_idx,
                             uint64_t& total_coverage,
                             size_t one_pct)
{
	stack<DFSStackEntry> dfs_stack;
	uint64_t current_level1_ticket_idx = 0;

	unique_ptr<vector<bool> > charged_level2_ticket_idxs(new vector<bool>(ticket_nodes.size()));

	dfs_stack.push(DFSStackEntry(start_ticket_idx, true, false));

	while (!dfs_stack.empty()) {

		DFSStackEntry& visit_node = dfs_stack.top();
		//sempre na primeira iteração vai ser falso invetido entra para marcar a visita
		if (!visit_node.is_visited) {

			visit_node.is_visited = 1;

			if (visit_node.is_ticket){

				TicketNode& t_node = ticket_nodes[visit_node.index];
				//verifica se e o ticket atual visitado
				bool is_start_ticket = (visit_node.index == start_ticket_idx);
				if (!visit_node.is_level_two) {

					//impede que delete o ticket do top que foi o selecionado
					if (!is_start_ticket && t_node.is_covered) {
						dfs_stack.pop();
						continue;
					}


					for (vector<uint64_t>::const_iterator m_idx = t_node.match_indexes.begin();
						m_idx != t_node.match_indexes.end(); ++m_idx)
					{
						dfs_stack.push(DFSStackEntry(*m_idx, false, !is_start_ticket));
					}

					//não entr ana primeira iteração
					if (!is_start_ticket) {

						t_node.is_covered = 1;
						
						t_node.remaining_coverage -= std::min<uint64_t>(t_node.remaining_coverage, 1);

						current_level1_ticket_idx = visit_node.index;
						charged_level2_ticket_idxs.reset(new vector<bool>(ticket_nodes.size()));
						(*charged_level2_ticket_idxs)[visit_node.index] = true;
					}

				} else {

	
				cerr << "SHOULD NOT BE HERE!!" << endl;
				}

			} else {

				MatchNode& m_node = garantias_nodes[visit_node.index];

				if (!visit_node.is_level_two) {

				for (vector<uint64_t>::const_iterator t_idx = m_node.ticket_indexes.begin();
					t_idx != m_node.ticket_indexes.end(); ++t_idx)
					{
						TicketNode& t_node = ticket_nodes[*t_idx];

						t_node.remaining_coverage -= std::min<uint32_t>(t_node.remaining_coverage, 1);

						if (!t_node.is_covered) {
							dfs_stack.push(DFSStackEntry(*t_idx, true, false));
						}
					}

				} else {

					// Second-level match node (appearing on level 3 of the overall tree),
					// i.e. a match contained by one of the tickets that was covered by
					// the most recent selection.

					// Charge its children. We can do this directly without needing to
					// push these children onto the stack. Each child represents a ticket
					// that is losing the potential to cover the newly-covered ticket that
					// is the root of the subtree we are currently traversing.
					for (vector<uint64_t>::const_iterator t_idx = m_node.ticket_indexes.begin();
					t_idx != m_node.ticket_indexes.end(); ++t_idx)
					{

						// Make sure we do not double-charge any one ticket within the
						// same subtree
						// Certifique-se de não cobrar duas vezes nenhum bilhete dentro do
						// mesma subárvore
						if (!(*charged_level2_ticket_idxs)[*t_idx]) {

							TicketNode& t_node = ticket_nodes[*t_idx];
							// Cobrança por incapacidade de cobrir o atual nível-2 (do total
							// árvore) bilhete
							t_node.remaining_coverage -= std::min<uint64_t>(t_node.remaining_coverage, 1);
							(*charged_level2_ticket_idxs)[*t_idx] = true;
						}
					}

					dfs_stack.pop();
				}
			}

		} else {

			// Have already traversed the subtree rooted at this node. Pop it and go
			// to its parent.

				dfs_stack.pop();
		}
	}
}

/**
 * Generates a lottery wheel in a naiively greedy manner by continually
 * selecting the ticket with the largest remaining coverage potential, until the
 * largest remaining coverage potential is zero.
 **/

static void generateWheel(std::vector<boost::dynamic_bitset<>>& all_tickets,
                          std::vector<boost::dynamic_bitset<>>& todas_garantias,
                          std::vector<uint64_t>& wheel_ticket_idxs)
{
	vector<TicketNode> ticket_nodes;
	vector<MatchNode> garantias_nodes;

	uint64_t total_coverage = 0;//,criado para o status do programa info...
	bool is_first_iteration = true;
	bool done = false;
	size_t one_pct;


	generateNodes(all_tickets, todas_garantias, ticket_nodes, garantias_nodes);
	
	one_pct = std::max(ticket_nodes.size() / 100, static_cast<size_t>(1));

	cout << "Gerando Roda da loteria..." << endl;
	vector<uint64_t> idx_remaning;
	for(uint64_t r=0; r<all_tickets.size(); ++r) 
		idx_remaning.push_back(r);
	while (!done) {

		uint64_t start_ticket_idx;

		if (is_first_iteration) {

			unsigned long seed1 = std::chrono::system_clock::now().time_since_epoch().count();
			std::mt19937_64 eng(seed1);
			std::uniform_int_distribution<unsigned int> distr(0, ticket_nodes.size()-1);
			//start_ticket_idx = 0;

			start_ticket_idx = distr(eng);

			is_first_iteration = false;

		} else {

			start_ticket_idx = 0;

			uint64_t best_coverage_sz = 0;
			vector<uint64_t> best_coverage_ticket_idxs;


			for (uint64_t ticket_idx = 0; ticket_idx < ticket_nodes.size(); ++ticket_idx) {
			uint64_t remaining_coverage = ticket_nodes[ticket_idx].remaining_coverage;
				if (remaining_coverage > best_coverage_sz) {
					best_coverage_ticket_idxs.clear();
					best_coverage_ticket_idxs.push_back(ticket_idx);
					best_coverage_sz = remaining_coverage;
				} else if (remaining_coverage == best_coverage_sz) {
					best_coverage_ticket_idxs.push_back(ticket_idx);
				}
			}

			// cout << "\t Next best coverage is " << best_coverage_sz << " (by "
			//      << best_coverage_ticket_idxs.size() << " tickets)" << endl;

			if (best_coverage_sz == 0) {
				done = true;
				cout << "Concluido." << endl;
				break;
			}

			// If more than one ticket has maximal coverage potential, select randomly
			// from among the set that do.
			unsigned seed1 = std::chrono::system_clock::now().time_since_epoch().count();
			std::mt19937_64 eng(seed1);
			std::uniform_int_distribution<unsigned int> distr(0, best_coverage_ticket_idxs.size()-1);

			start_ticket_idx = best_coverage_ticket_idxs[distr(eng)];
			// bool foiCoberto = false;

			// 	for (int i=0; i< wheel_ticket_idxs.size();++i){


			// 		for (int j =0;  j < ticket_nodes[wheel_ticket_idxs[i]].match_indexes.size(); ++j){

			// 			for (int k = 0; k < ticket_nodes[start_ticket_idx].match_indexes.size(); ++k){

			// 				if (ticket_nodes[start_ticket_idx].match_indexes[k] == ticket_nodes[wheel_ticket_idxs[i]].match_indexes[j]) {
			// 					ticket_nodes[start_ticket_idx].remaining_coverage-= std::min<uint32_t>(ticket_nodes[start_ticket_idx].remaining_coverage, 1);

			// 					foiCoberto=true;
			// 					//break;
			// 				}
			// 			}

			// 			// if (foiCoberto)
			// 			// 	break;
			// 		}

			// 		// if (foiCoberto)
			// 		// 	break;

			// 	}
			// 	if (foiCoberto){

			// 		continue;
			// 	}
			}
			wheel_ticket_idxs.push_back(start_ticket_idx);
			ticket_nodes[start_ticket_idx].remaining_coverage = 0;
			ticket_nodes[start_ticket_idx].is_covered = 1;
			//updatePotentials(ticket_nodes, garantias_nodes, start_ticket_idx,total_coverage, one_pct);
						
			updateSimpleCovered( all_tickets,ticket_nodes,start_ticket_idx,qtd_dez_garante_acertos,idx_remaning);
    
	}

  //cout << "Done." << endl;
}
const std::string currentDateTime() {
    time_t     now = time(0);
    struct tm  tstruct;
    char       buf[80];
    tstruct = *localtime(&now);
    // Visit http://en.cppreference.com/w/cpp/chrono/c/strftime
    // for more information about date/time format
    strftime(buf, sizeof(buf), "%Y-%m-%d_%Hh%Mmin%Sseg", &tstruct);

    return buf;
}

int main(int argc, char *argv[])
{
	std::vector<boost::dynamic_bitset<>> all_tickets;
	std::vector<boost::dynamic_bitset<>> todas_garantias;

  	int qtdBusca=0;
  // Prompt for problem parameters. In addition to sanity checks, we enforce the
  // following restrictions:
  //
  // 1. Range must be less than 64 (or else we cannot represent any given ticket
  //    in a uint64_t)
  //
  // 2. The combination of range and ticket size cannot generate more than 2^30
  //    tickets (or else we cannot cram a DFStackEntry struct into 32 bits and
  //    our memory requirements explode)
  //
  // 3. Match sizes cannot be larger than 16, due to implementation details of
  //    generateAllCombos (in combinatorics.cc). Matches larger than 16 are
  //    pretty impractical anyway, so I saw no need to complicate that
  //    function's implementation to support such match sizes.
  // Solicita par�metros do problema. Al�m das verifica��es de sanidade, aplicamos a
   // seguintes restri��es:
   //
   // 1. O intervalo deve ser menor que 64 (caso contr�rio, n�o podemos representar nenhum ticket
   // em um uint64_t)
   //
   // 2. A combina��o de intervalo e tamanho do ticket n�o pode gerar mais de 2^30
   // tickets (ou ent�o n�o podemos colocar uma estrutura DFStackEntry em 32 bits e
   // nossos requisitos de mem�ria explodem)
   //
   // 3. Os tamanhos de correspond�ncia n�o podem ser maiores que 16, devido aos detalhes de implementa��o de
   // gereAllCombos (em combinatorics.cc). Correspond�ncias maiores que 16 s�o
   // bastante impratic�vel de qualquer maneira, ent�o n�o vi necessidade de complicar isso
   // implementa��o da fun��o para suportar tais tamanhos de correspond�ncia.


  if (argc ==5)	qtd_dezenas_jogo = atoi(argv[1]);
  else{
	  cout << "Digite quantidade de dezenas da loteria: ";
	  cin >> qtd_dezenas_jogo;
	}
 // qtd_dezenas_jogo = 6;
  if (qtd_dezenas_jogo > 64) {
    cerr << "Ranges larger than 64 are not supported." << endl;
    return -1;
  }
  if (argc ==5)
  	qtd_dezenas_sorteio = atoi(argv[2]);
  else{

	  cout << "digite quantidade de dezenas sorteadas: ";
	  cin >> qtd_dezenas_sorteio;
	}
 	// qtd_dezenas_sorteio = 3;

  if (qtd_dezenas_sorteio > qtd_dezenas_jogo) {
    cerr << "Ticket size cannot be larger than range (that makes no sense!)" << endl;
    return -1;
  } else if ( comb(qtd_dezenas_jogo, qtd_dezenas_sorteio) >= (1ul << 30) ) {
    cerr << "This combination of range and ticket size would generate too many tickets ("
         << comb(qtd_dezenas_jogo, qtd_dezenas_sorteio) << ")." << endl;
    cerr << "This program only supports quantities of tickets less than 2^30 ("
         << (1ul << 30) << ")." << endl;
    return -1;
  }
    if (argc ==5)	qtd_dez_garante_acertos = atoi(argv[3]);
	else{

		cout << "digite quantidade de dezenas da  garantia: ";
		cin >> qtd_dez_garante_acertos;
	}
//  qtd_dez_garante_acertos = 2;
	  if (qtd_dez_garante_acertos > qtd_dezenas_sorteio) {
	    cerr << "Match size cannot be larger than ticket size (that makes no sense!)" << endl;
	    return -1;
	  } else if (qtd_dez_garante_acertos > 16) {
	    cerr << "Match sizes larger than 16 are not supported." << endl;
	    return -1;
	  }
	if (argc ==5)qtdBusca = atoi(argv[4]);
	else{
		cout << "Enter quantidade de tentativas para busca: ";
		cin >> qtdBusca;
	}
  // First, generate all tickets and matches. When generateWheel is called, the
  // information about these tickets and matches will be forgotten to save
  // memory, but their relationship structure is preserved in the problem graph.
  // Primeiro, gere todos os tickets e partidas. Quando o generateWheel � chamado, o
   // informa��es sobre esses ingressos e partidas ser�o esquecidas para salvar
   // mem�ria, mas sua estrutura de relacionamento � preservada no gr�fico do problema.
	vector<uint64_t> wheel_ticket_idxsCopy;
	vector<uint64_t> wheel_ticket_idxs;
	cout << "Gerar todos os tickets possiveis...";
	cout.flush();
	boost::dynamic_bitset<> dezenas_jogo(qtd_dezenas_jogo);
	//gerar todos os tickets possiveis
	generateCombinations(dezenas_jogo,0,qtd_dezenas_sorteio, all_tickets);
	cout << "done. (generated " << all_tickets.size() << " tickets)" << endl;

	// cout << "Generating all possible " << qtd_dez_garante_acertos << "-garantia...";
	// cout.flush();
	//dezenas_jogo.reset();
	//gerar todas garantias possiveis
	// generateCombinations(dezenas_jogo, 0,qtd_dez_garante_acertos ,todas_garantias);
	// cout << "done. (generated " << todas_garantias.size() << " "
	// 	<< qtd_dez_garante_acertos << "-combinacoes de garantia)" << endl;
  	menorAposta=all_tickets.size();
   for (int i=0;i< qtdBusca;i++){

  // Actually do the hard work of generating the wheel
  // Na verdade, faz o trabalho duro de gerar a roda

	generateWheel(all_tickets, todas_garantias, wheel_ticket_idxsCopy);

	if ( menorAposta > wheel_ticket_idxsCopy.size() ){
		menorAposta = wheel_ticket_idxsCopy.size();
		wheel_ticket_idxs = wheel_ticket_idxsCopy;

		//system("pause");
	}
   	// for (int i=0; i< wheel_ticket_idxs.size();++i)
	// 	tentativa_idx_map[wheel_ticket_idxs[i]]=i;

	cout << "total apostas "<< wheel_ticket_idxs.size() << endl;
	cout << "Tentava "<< i+1 <<" de "<<qtdBusca<< endl;
	wheel_ticket_idxsCopy.clear();

  }

  // Re-generate all the ticket so we can convert the ticket indexes that
  // generateWheel gave us back into actual tickets with numbers on them. This
  // works since generateAllTickets always produces tickets in the same
  // deterministic order.
  // Gera novamente todo o ticket para que possamos converter os �ndices de ticket que
   // generateWheel nos devolveu os tickets reais com n�meros neles. este
   // funciona desde que generateAllTickets sempre produz tickets no mesmo
   // ordem determin�stica.
  //cout << "Re-generating all possible tickets...";
 // cout.flush();
  //generateCombinations(dezenas_jogo,0,qtd_dezenas_sorteio, all_tickets);
  cout << "done. (generated " << all_tickets.size() << " tickets)" << endl;

	cout<<"\n";
  stringstream sstr_wheel_savename;

  sstr_wheel_savename << "wheel-" << qtd_dezenas_jogo << "-" << qtd_dezenas_sorteio << "-"
  << qtd_dez_garante_acertos<<"_" << currentDateTime() << ".txt";

  ofstream outfile(sstr_wheel_savename.str().c_str());

  cout << "Wheel is: " << endl;
  for (vector<uint64_t>::const_iterator t_idx = wheel_ticket_idxs.begin();
       t_idx != wheel_ticket_idxs.end(); ++t_idx)
    {
      cout << "\t" << ticketToString(all_tickets[*t_idx]) << endl;
      outfile << ticketToString(all_tickets[*t_idx]) << endl;
    }

  cout << "Wrote wheel to file " << sstr_wheel_savename.str() << endl;

  return 0;
}

