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
#include <iomanip>
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
#include "wheelgen.h"
#include "combinacao.h"
#include <random>
#include <chrono>
#include <time.h>
#include <algorithm>
#include <boost/dynamic_bitset.hpp>
#include <set>

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

 ///< numeros da loteriaRange size (r), e.g. a total de dezenas no sorteio exemplo mega-sena 60 dezenas.
//static size_t   ///< Ticket size (t), quantidade de dezenas que vao ser sorteadas exemplo mega-sena 6

static size_t qtdBusca,permitirSobreposicao,qtd_dezenas_jogo,menorAposta;
static size_t qtd_dez_garante_acertos,qtd_dezenas_sorteio,qtd_jogos ;  ///< quantidade de dezenas de garantia de acertos

 ///< busca para aceitar o menor numero de combincao
  /** < Match size (m), quantidade de dezenas que queremos garantir de acertos no jogo
exemplo mega-sena sorteia 6 dezenas queremos garantir 5 ent�o a garantia sera 5 */
//unordered_map<uint64_t, uint64_t> tentativa_idx_map;
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
static std::vector<int> convertBitsetFechamento(boost::dynamic_bitset<> numerosbit,vector<int> fechamento){
	std::vector<int> bit_vector;
	std::size_t pos = numerosbit.find_first();
	while (pos != boost::dynamic_bitset<>::npos) {
		bit_vector.push_back(fechamento[pos]);
		pos = numerosbit.find_next(pos);
	}
	return bit_vector;
}

/**
 * Builds the first part of the problem graph by creating a MatchNode struct for
 * each match in the todas_garantias vector.
 **/
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
static void convertTicketsToTicketNodes(std::vector<boost::dynamic_bitset<>>& all_tickets,
std::vector<TicketNode>& ticket_nodes,unordered_map<boost::dynamic_bitset<>, uint64_t> garantias_idx_map,
std::vector<MatchNode>& garantias_nodes)
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

		vector<vector<int>> matches_for_ticket;
		vector<int> entrada= convertBitsetNum(*t);
		geraCombinacoes(entrada, qtd_dez_garante_acertos, matches_for_ticket);

		for (vector<vector<int>>::const_iterator m = matches_for_ticket.begin();
			m != matches_for_ticket.end();++garantias_idx, ++m)
		{

				uint64_t garantias_idx = (garantias_idx_map.find(convertNumBitset((*m),(*t).size())))->second;
				ticket_nodes[ticket_idx].match_indexes.push_back(garantias_idx);
				garantias_nodes[garantias_idx].ticket_indexes.push_back(ticket_idx);
			//std::cout<<i<<"\n";
			// system("pause");

		}


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
 unordered_map<boost::dynamic_bitset<>, uint64_t> garantias_idx_map(todas_garantias.size());

  cout << "Indexando todas garantias...";
  cout.flush();
  convertMatchesToMatchNodes(todas_garantias, garantias_nodes, garantias_idx_map);
  todas_garantias.clear();
  todas_garantias.reserve(0);

  cout << "done." << endl;

  cout << "Indexando todos tickets...";
  cout.flush();
  convertTicketsToTicketNodes(all_tickets, ticket_nodes,garantias_idx_map,garantias_nodes);
  garantias_idx_map.clear();
  garantias_idx_map.reserve(0);
  all_tickets.clear();
  all_tickets.reserve(0);

   cout << "done." << endl;
}


/**
 * This is the part that makes this generator fast. Here we do an efficient
 * depth-first walk of the problem graph and update the coverage potentials of
 * all tickets based on the ticket that we just selected for the wheel. Because
 * the coverage potentials are kept accurate, the selection of the next ticket
 * can always be done in O(n) time.
 **/
static void updateSimpleCovered(std::vector<boost::dynamic_bitset<>>& all_tickets,std::vector<TicketNode>& ticket_nodes,std::vector<uint64_t> rodaLoteria,uint64_t acertoGarantia ){

	int idxRoda=0;
	bool cobre=false;
	for (uint64_t i = 0; i < all_tickets.size(); i++){
		if(ticket_nodes[i].is_covered)continue;
		uint64_t potencialCobre=0;
		if(idxRoda<rodaLoteria.size()){
			if(rodaLoteria[idxRoda]==i){
				idxRoda++;
				continue;
			}
			boost::dynamic_bitset<> ver = all_tickets[rodaLoteria[idxRoda]]&all_tickets[i];
			idxRoda++;
			if (ver.count()==acertoGarantia)continue;

		}else
			idxRoda=0;

		for (uint64_t j = 0;j < all_tickets.size(); j++){
			if(i==j)continue;
			if(idxRoda<rodaLoteria.size()){
				if(rodaLoteria[idxRoda]==j){
					idxRoda++;
					continue;
				}
				boost::dynamic_bitset<> ver = all_tickets[rodaLoteria[idxRoda]]&all_tickets[j];
				idxRoda++;
				if (ver.count()==acertoGarantia){
					continue;
				}


			}else{
				idxRoda=0;
			}
			boost::dynamic_bitset<> ver = all_tickets[i]&all_tickets[j];
			//std::cout<<j<<" ";
			if (ver.count()==acertoGarantia){
				potencialCobre++;
			}

		}
		ticket_nodes[i].remaining_coverage=potencialCobre++;

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


					// Se o no nao for coberto recentemente, coloque todos os seus filhos (que sao
					// corresponde aos nos) na pilha DFS a ser visitada

					for (vector<uint32_t>::const_iterator m_idx = t_node.match_indexes.begin();
						m_idx != t_node.match_indexes.end(); ++m_idx)
					{
						dfs_stack.push(DFSStackEntry(*m_idx, false, !is_start_ticket));
					}

					//não entr ana primeira iteração
					if (!is_start_ticket) {

						// Marca o no como coberto

						t_node.is_covered = 1;

						// Charge for inability to cover self
						// Cobranca por incapacidade de cobrir a si mesmo
						t_node.remaining_coverage -= std::min<uint64_t>(t_node.remaining_coverage, 1);

						current_level1_ticket_idx = visit_node.index;
						charged_level2_ticket_idxs.reset(new vector<bool>(ticket_nodes.size()));
						(*charged_level2_ticket_idxs)[visit_node.index] = true;
					}

				} else {


				// Este seria um no de ticket de segundo nivel, ou seja, um ticket que
				// tendo seu potencial de cobertura reduzido em decorrencia da ultima
				// selecaoo. No entanto, a travessia DFS nunca deve realmente atingir
				// aqui porque fazemos as reducoes potenciais dos nos de correspondencia,
				// para reduzir o numero de iteracoes por meio do codigo DFS.

				cerr << "SHOULD NOT BE HERE!!" << endl;
				}

			} else {

				MatchNode& m_node = garantias_nodes[visit_node.index];

				if (!visit_node.is_level_two) {

					// Nó de correspondência de primeiro nível, ou seja, uma correspondência contida pelo recém-selecionado// bilhete.
					// Coloca cada um de seus filhos descobertos (nós de ticket) na pilha DFS
					for (vector<uint64_t>::const_iterator t_idx = m_node.ticket_indexes.begin();
					t_idx != m_node.ticket_indexes.end(); ++t_idx)
					{
						TicketNode& t_node = ticket_nodes[*t_idx];

						// Cobrança por incapacidade de cobrir  o ticket do topo
						//esse ticket do topo cobriu antes desses então a redução para que ele possa cobrir
						//qualquer outros menos esses
						t_node.remaining_coverage -= std::min<uint64_t>(t_node.remaining_coverage, 1);

						// Só insere no de garantia se ela estiver descoberta, pois não precisamos fazer
						// quaisquer reduções de cobertura nas subárvores já cobertas
						// nós de ticket.
						if (!t_node.is_covered) {
							dfs_stack.push(DFSStackEntry(*t_idx, true, false));
						}
					}

				} else {

					//v/ Second-level match node (appearing on level 3 of the overall tree),
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

  if (ticket_nodes_cp.empty()){
  	generateNodes(all_tickets, todas_garantias, ticket_nodes, garantias_nodes);
	if(qtdBusca > 1){
		ticket_nodes_cp = ticket_nodes;
		garantias_nodes_cp =  garantias_nodes;
		}
  }else{
	if(qtdBusca>1){
		ticket_nodes = ticket_nodes_cp;
		garantias_nodes = garantias_nodes_cp;
	}
  }

  one_pct = std::max(ticket_nodes.size() / 100, static_cast<size_t>(1));

  cout << "Gerando Roda da loteria..." << endl;

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

		if(permitirSobreposicao==0){
			bool foiCoberto = false;

			for (int i=0; i< wheel_ticket_idxs.size();++i){

				for (int j =0;  j < ticket_nodes[wheel_ticket_idxs[i]].match_indexes.size(); ++j){

					for (int k = 0; k < ticket_nodes[start_ticket_idx].match_indexes.size(); ++k){

						if (ticket_nodes[start_ticket_idx].match_indexes[k] == ticket_nodes[wheel_ticket_idxs[i]].match_indexes[j]) {
							ticket_nodes[start_ticket_idx].remaining_coverage-= std::min<uint64_t>(ticket_nodes[start_ticket_idx].remaining_coverage, 1);

							foiCoberto=true;
							break;
						}
					}

					if (foiCoberto)
					 	break;
				}

				if (foiCoberto)
				 	break;

			}
			if (foiCoberto){

				continue;
			}
		}
	}
	wheel_ticket_idxs.push_back(start_ticket_idx);
    ticket_nodes[start_ticket_idx].remaining_coverage = 0;
    ticket_nodes[start_ticket_idx].is_covered = 1;

    if( wheel_ticket_idxs.size() > menorAposta){
      done = true;
	  cout << "Concluido, ja possui uma cobertura igual menor." << endl;
      break;
    }

	updatePotentials(ticket_nodes, garantias_nodes, start_ticket_idx,total_coverage, one_pct);
	//updateSimpleCovered( all_tickets,ticket_nodes,wheel_ticket_idxs,qtd_dez_garante_acertos );

    //cout << "\t " << wheel_ticket_idxs.size() << " tickets selected for wheel." << endl;
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
    strftime(buf, sizeof(buf), "%d-%m-%Y_%Hh%Mmin%Sseg", &tstruct);

    return buf;
}
std::string getCurrentDateTime() {
    std::time_t t = std::time(nullptr);
    std::tm tm = *std::localtime(&t);
    std::ostringstream oss;
    oss << std::put_time(&tm, "%d-%m-%Y_%Hh%Mmin%Sseg");
    return oss.str();
}

// Função para salvar apostasTotais em um arquivo .txt no formato desejado
void saveApostasTotaisToFile(const std::vector<std::vector<int>>& apostasTotais,
                             int qtd_dezenas_jogo, int qtd_dezenas_sorteio, int qtd_dez_garante_acertos) {
    // Calcula a quantidade de jogos
    size_t qtdNumeroJogo = apostasTotais.size();

    // Imprime informações sobre a quantidade de apostas e os intervalos

    // Nome do arquivo com data e hora
    std::string filename = "jogos_" + std::to_string(qtd_dezenas_jogo) +
                           "_" + std::to_string(qtd_dezenas_sorteio) + "_"+std::to_string(qtd_dez_garante_acertos)+"_"
                           std::to_string(qtdNumeroJogo) + "_" + getCurrentDateTime() + ".txt";

    // Abre o arquivo para escrita
    std::ofstream outFile(filename);

    if (!outFile) {
        std::cerr << "Não foi possível abrir o arquivo para gravação." << std::endl;
        return;
    }

    // Grava o conteúdo de apostasTotais no arquivo
    for (const auto& aposta : apostasTotais) {
        for (size_t i = 0; i < aposta.size(); ++i) {
            outFile << aposta[i];
            if (i < aposta.size() - 1) {
                outFile << ';';  // Separador entre os números
            }
        }
        outFile << std::endl;  // Nova linha após cada aposta
    }

    outFile.close();
    std::cout << "Dados gravados com sucesso no arquivo: " << filename << std::endl;
}
void eliminaNumPosicao(std::vector<std::vector<int>>& jogosGerados) {
    std::vector<int> listaRemove;

    for (size_t i = 0; i < jogosGerados.size(); ++i) {
        // casa 1 não entra números maior ou igual a 5
        if (jogosGerados[i][0] >= 5) {
            listaRemove.push_back(i);
        }
        // casa 2 não entra números maior ou igual a 8
        else if (jogosGerados[i][1] >= 8) {
            listaRemove.push_back(i);
        }
        // casa 3 não entra números maior ou igual a 10
        else if (jogosGerados[i][2] >= 10) {
            listaRemove.push_back(i);
        }
        // casa 4 não entra números maior ou igual a 11
        else if (jogosGerados[i][3] >= 11) {
            listaRemove.push_back(i);
        }
        // casa 5 não entra números maior ou igual a 13
        else if (jogosGerados[i][4] >= 13) {
            listaRemove.push_back(i);
        }
        // casa 6 não entra o número 6 e números maior ou igual a 15
        else if (jogosGerados[i][5] == 6 || jogosGerados[i][5] >= 15) {
            listaRemove.push_back(i);
        }
        // casa 7 não entra o número 7 e números maior ou igual a 16
        else if (jogosGerados[i][6] == 7 || jogosGerados[i][6] >= 16) {
            listaRemove.push_back(i);
        }
        // casa 8 não entra o número 8 e números maior ou igual a 18
        else if (jogosGerados[i][7] == 8 || jogosGerados[i][7] >= 18) {
            listaRemove.push_back(i);
        }
        // casa 9 não entra o número 9 e números maior ou igual a 19
        else if ((jogosGerados[i][8] >= 9 && jogosGerados[i][8] <= 10) || jogosGerados[i][8] >= 19) {
            listaRemove.push_back(i);
        }
        // casa 10 não entra o número menor ou igual a 11
        else if (jogosGerados[i][9] <= 11) {
            listaRemove.push_back(i);
        }
        // casa 11 não entra o número menor ou igual a 13
        else if (jogosGerados[i][10] <= 13) {
            listaRemove.push_back(i);
        }
        // casa 12 não entra o número menor ou igual a 15
        else if (jogosGerados[i][11] <= 15) {
            listaRemove.push_back(i);
        }
        // casa 13 não entra os números menor ou igual a 17
        else if (jogosGerados[i][12] <= 17) {
            listaRemove.push_back(i);
        }
        // casa 14 não entra os números menor ou igual a 19
        else if (jogosGerados[i][13] <= 19) {
            listaRemove.push_back(i);
        }
        // casa 15 não entra os números menor ou igual a 21
        else if (jogosGerados[i][14] <= 21) {
            listaRemove.push_back(i);
        }
    }

    // Remove os elementos de jogosGerados
    for (int i = listaRemove.size() - 1; i >= 0; --i) {
        jogosGerados.erase(jogosGerados.begin() + listaRemove[i]);
    }
}
void eliminaNumSequencia(int numSeq, std::vector<std::vector<int>>& possibilidades) {
    std::vector<int> listaRemove;
    int conta = 0;

    for (const auto& dz : possibilidades) {
        int sequencia = 1;
        int sequenciaMaior = 1;

        for (size_t i = 1; i < dz.size(); ++i) {
            if (dz[i - 1] == dz[i] - 1) {
                sequencia += 1;
                if (sequenciaMaior < sequencia) {
                    sequenciaMaior = sequencia;
                }
            } else {
                sequencia = 1;
            }
        }

        if (sequenciaMaior == 2 || sequenciaMaior > numSeq) {
            listaRemove.push_back(conta);
        }

        conta += 1;
    }

    // Remove os elementos da lista `possibilidades`
    for (int i = listaRemove.size() - 1; i >= 0; --i) {
        possibilidades.erase(possibilidades.begin() + listaRemove[i]);
    }
}
void eliminaMaiorGap(int numGap, std::vector<std::vector<int>>& jogosGerados) {
    for (auto it = jogosGerados.begin(); it != jogosGerados.end();) {
        bool remove = false;
        for (size_t j = 1; j < it->size(); ++j) {
            int gap = (*it)[j] - (*it)[j - 1];
            if (gap > numGap) {
                remove = true;
                break;
            }
        }
        if (remove) {
            it = jogosGerados.erase(it);
        } else {
            ++it;
        }
    }
}

std::vector<std::vector<int>> obter_resultados(const std::string& nomeArquivo) {
    std::ifstream arquivo(nomeArquivo);
    std::vector<std::vector<int>> dados;
    std::string linha;

    // Ignora a primeira linha (cabeçalho)
    std::getline(arquivo, linha);

    while (std::getline(arquivo, linha)) {
        std::stringstream ss(linha);
        std::string valor;
        std::vector<int> linhaDados;

        // Ignora a primeira coluna (seq)
        std::getline(ss, valor, ';');
        std::getline(ss, valor, ';');


        // Lê as colunas n1 até n15
        for (int i = 0; i < 15; ++i) {
            if (std::getline(ss, valor, ';')) {
                linhaDados.push_back(std::stoi(valor));
            }
        }

        dados.push_back(linhaDados);
    }

    return dados;
}


void remove15E14Num( const std::vector<std::vector<int>>& resultSorteio, std::vector<std::vector<int>>& jogosGerados) {
    std::set<int> listaRemove;

    for (size_t i = 0; i < resultSorteio.size(); ++i) {
        int cont = 0;

        for (const auto& j : jogosGerados) {
            if (listaRemove.find(cont) == listaRemove.end()) {
                if (resultSorteio[i] == j) {
                    listaRemove.insert(cont);
                } else {
                    // Calcula a interseção dos conjuntos
                    std::vector<int> intersection;
                    std::set_intersection(resultSorteio[i].begin(), resultSorteio[i].end(),
                                          j.begin(), j.end(),
                                          std::back_inserter(intersection));
                    if (intersection.size() == 14) {
                        listaRemove.insert(cont);
                    }
                }
            }
            cont++;
        }
    }

    // Remove os elementos da lista `jogosGerados`
    for (auto it = listaRemove.rbegin(); it != listaRemove.rend(); ++it) {
        jogosGerados.erase(jogosGerados.begin() + *it);
    }
}


int main(int argc, char *argv[])
{
	std::vector<boost::dynamic_bitset<>> all_tickets;
	std::vector<boost::dynamic_bitset<>> todas_garantias;

  	qtdBusca=0;
	int qtdArgc = 7;
  if (argc ==qtdArgc)	qtd_dezenas_jogo = atoi(argv[1]);
  else{
	  cout << "Digite quantidade de dezenas da loteria: ";
	  cin >> qtd_dezenas_jogo;
	}

  if (qtd_dezenas_jogo > 64) {
    cerr << "Ranges larger than 64 are not supported." << endl;
    return -1;
  }
  if (argc ==qtdArgc)
  	qtd_dezenas_sorteio = atoi(argv[2]);
  else{

	  cout << "digite quantidade de dezenas sorteadas: ";
	  cin >> qtd_dezenas_sorteio;
	}

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
    if (argc ==qtdArgc)	qtd_dez_garante_acertos = atoi(argv[3]);
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
	if (argc ==qtdArgc)qtdBusca = atoi(argv[4]);
	else{
		cout << "Entre com quantidade de tentativas de buscas: ";
		cin >> qtdBusca;
	}
	if (argc ==qtdArgc)permitirSobreposicao = atoi(argv[5]);
	else{
		cout << "permitir sobreposicao, digite 1 para sim 0 para nao: ";
		cin >> permitirSobreposicao;
	}
	if (argc ==qtdArgc)qtd_jogos = atoi(argv[6]);
	else{
		cout << "Digite a quantidades de jogos: ";
		cin >> qtd_jogos;
	}

	vector<uint64_t> wheel_ticket_idxsCopy;
	vector<uint64_t> wheel_ticket_idxs;
	cout << "Gerar todos os tickets possiveis...";
	cout.flush();
	boost::dynamic_bitset<> dezenas_jogo(qtd_dezenas_jogo);
	//gerar todos os tickets possiveis
	generateAllCombos(dezenas_jogo,0,qtd_dezenas_sorteio, all_tickets);
	cout << "done. (generated " << all_tickets.size() << " tickets)" << endl;

	cout << "Generating all possible " << qtd_dez_garante_acertos << "-garantia...";
	cout.flush();
	dezenas_jogo.reset();
	//gerar todas garantias possiveis
	generateAllCombos(dezenas_jogo, 0,qtd_dez_garante_acertos ,todas_garantias);
	cout << "done. (generated " << todas_garantias.size() << " "
		<< qtd_dez_garante_acertos << "-combinacoes de garantia)" << endl;
  	menorAposta=all_tickets.size();
  for (size_t i=0;i< qtdBusca;i++){

	generateWheel(all_tickets, todas_garantias, wheel_ticket_idxsCopy);

	if ( menorAposta > wheel_ticket_idxsCopy.size() ){
		menorAposta = wheel_ticket_idxsCopy.size();
		wheel_ticket_idxs = wheel_ticket_idxsCopy;

		//system("pause");
	}

	cout << "total apostas "<< wheel_ticket_idxs.size() << endl;
	cout << "Tentava "<< i+1 <<" de "<<qtdBusca<< endl;
	wheel_ticket_idxsCopy.clear();

  }
	//permitirSobreposicao=0;
	std::vector<std::vector<int>> apostasTotais;
	std::vector<std::vector<int>> combinacoes;
  cout.flush();

  vector<int> dez;
  std::vector<std::vector<int>> resultados = obter_resultados("D:/programacao/LotoGanhaFacil/base/resultados.csv");
  for (size_t k = 1; k < 26; k++)
	dez.push_back(k);
	geraCombinacoes(dez, qtd_dezenas_jogo, combinacoes);

	for (size_t i = 0; i < qtd_jogos; i++)
	{

		unsigned long seed1 = std::chrono::system_clock::now().time_since_epoch().count();
    	 std::mt19937_64 eng(seed1);
    	 std::uniform_int_distribution<unsigned int> distr(0, combinacoes.size()-1);
	   	int idx = distr(eng);

		generateAllCombos(dezenas_jogo,0,qtd_dezenas_sorteio, all_tickets);
		cout << "done. (generated " << all_tickets.size() << " tickets)" << endl;

		for (vector<uint64_t>::const_iterator t_idx = wheel_ticket_idxs.begin();
		t_idx != wheel_ticket_idxs.end(); ++t_idx)
		{
			//cout << "\t" << ticketToString(all_tickets[*t_idx]) << endl;
			vector<int> entrada= convertBitsetFechamento(all_tickets[*t_idx],combinacoes[idx]);
			apostasTotais.push_back(entrada);
			for (const auto& ent:entrada) cout<< ent<<";";
				cout<<endl;
			if (apostasTotais.size()==qtd_jogos)break;

		}
		int numGap = 5;
		remove15E14Num(resultados,apostasTotais);
   		eliminaMaiorGap(numGap, apostasTotais);
		eliminaNumPosicao(apostasTotais);
		eliminaNumSequencia(8,apostasTotais);
		if (apostasTotais.size()==qtd_jogos)break;
		wheel_ticket_idxs = wheel_ticket_idxsCopy;
		wheel_ticket_idxsCopy.clear();
		generateWheel(all_tickets, todas_garantias, wheel_ticket_idxsCopy);
		combinacoes.erase(combinacoes.begin() + idx);
	}

	cout<<"\n total Jogos "<<apostasTotais.size();
	saveApostasTotaisToFile(apostasTotais,qtd_dezenas_jogo,qtd_dezenas_sorteio);
//   stringstream sstr_wheel_savename;

//   sstr_wheel_savename << "wheel-" << qtd_dezenas_jogo << "-" << qtd_dezenas_sorteio << "-"
//   << qtd_dez_garante_acertos<<"_" << currentDateTime() << ".txt";

//   ofstream outfile(sstr_wheel_savename.str().c_str());

//   cout << "Wheel is: " << endl;

//   for (vector<uint64_t>::const_iterator t_idx = wheel_ticket_idxs.begin();
//        t_idx != wheel_ticket_idxs.end(); ++t_idx)
//   {
//       cout << "\t" << ticketToString(all_tickets[*t_idx]) << endl;
//       outfile << ticketToString(all_tickets[*t_idx]) << endl;
//   }

  //cout << "Salvar jogo " << sstr_wheel_savename.str() << endl;

  return 0;
}

