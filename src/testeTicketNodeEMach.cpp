#include <cstdint>
#include "wheelgen.h"
#include <stack>
#include <vector>
#include <iostream>
#include <unordered_map>
#include <algorithm>
#include <memory>
#include <boost/dynamic_bitset.hpp>
#include "GeraCombIterarBitSet.h"
#include "GeraCombIterar.h"
#include <random>
#include <chrono>

static std::string ticketToString(boost::dynamic_bitset<>&);

static void updateSimpleCovered(std::vector<boost::dynamic_bitset<>>& all_tickets,std::vector<TicketNode>& ticket_nodes,std::vector<uint64_t> rodaLoteria,uint64_t acertoGarantia ){
	
	int idxRoda=0;
	bool cobre=false;
	for (uint64_t i = 0; i < all_tickets.size(); i++){
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

static std::string ticketToString(boost::dynamic_bitset<>& bs){
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

static void updatePotentials(std::vector<TicketNode>& ticket_nodes, std::vector<MatchNode>& garantias_nodes, 
uint64_t start_ticket_idx )
 {
	std::stack<DFSStackEntry> dfs_stack;
	uint64_t current_level1_ticket_idx = 0;

	
	std::unique_ptr<std::vector<bool> > charged_level2_ticket_idxs(new std::vector<bool>(ticket_nodes.size()));

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
				
					for (std::vector<uint32_t>::const_iterator m_idx = t_node.match_indexes.begin();
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
						charged_level2_ticket_idxs.reset(new std::vector<bool>(ticket_nodes.size()));
						(*charged_level2_ticket_idxs)[visit_node.index] = true;
					}

				} else {
								
				std::cerr << "SHOULD NOT BE HERE!!" << std::endl;
				}
			
			} else {

				MatchNode& m_node = garantias_nodes[visit_node.index];
				
				if (!visit_node.is_level_two) {

					// Nó de correspondência de primeiro nível, ou seja, uma correspondência contida pelo recém-selecionado// bilhete.
					// Coloca cada um de seus filhos descobertos (nós de ticket) na pilha DFS
					for (std::vector<uint64_t>::const_iterator t_idx = m_node.ticket_indexes.begin();
					t_idx != m_node.ticket_indexes.end(); ++t_idx)
					{
						TicketNode& t_node = ticket_nodes[*t_idx];

						
						t_node.remaining_coverage -= std::min<uint32_t>(t_node.remaining_coverage, 1);

						// Só insere no de garantia se ela estiver descoberta, pois não precisamos fazer
						// quaisquer reduções de cobertura nas subárvores já cobertas
						// nós de ticket.
						if (!t_node.is_covered) {
							dfs_stack.push(DFSStackEntry(*t_idx, true, false));
						}
					}

				} else {

					
					for (std::vector<uint64_t>::const_iterator t_idx = m_node.ticket_indexes.begin();
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
static void generateCombinations(boost::dynamic_bitset<>& combination, int index, int remaining,  std::unordered_map<boost::dynamic_bitset<>, uint64_t>& garantias_idx_map, uint64_t & idxGarantias)
{
	if (remaining == 0)
	{
		
		garantias_idx_map[combination]=idxGarantias;
		idxGarantias++;
		return;
	}

	if (index >= combination.size())
	{
		return;
	}

	// Select the current number
	combination[index] = true;
	generateCombinations(combination, index + 1, remaining - 1,  garantias_idx_map,idxGarantias);

	// Do not select the current number
	combination[index] = false;
	generateCombinations(combination, index + 1, remaining,  garantias_idx_map,idxGarantias);
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


static int getMaxNum(std::vector<std::vector<int>> combination){
	int largest = INT_MIN;  // Initialize largest to the minimum possible value for an int

		for (const auto &inner_vec : combination) {
			for (int num : inner_vec) {
				largest = std::max(largest, num);  // Update largest if necessary
			}
		}
	    return largest;
}
static std::string vectorToString(std::vector<int>& comb){
	std::string vetorString = "[";
		for (int i = 0; i < comb.size(); i++) {
			vetorString += std::to_string(comb[i]);
			if(i<comb.size()-1)vetorString +=",";
		}
		vetorString += "]";
	return vetorString;
}
int main() {
	uint64_t qtd_dezenas_jogo=17,qtd_dezenas_sorteio=15,qtd_dez_garante_acertos=14;
	std::vector<int> entrada;
	for (int i = 1; i <= qtd_dezenas_jogo; i++)
	{
		entrada.push_back(i);
	}

	GeraCombIterarBitset tickets(qtd_dezenas_jogo,qtd_dezenas_sorteio);
	GeraCombIterarBitset ticketsCob(qtd_dezenas_jogo,qtd_dezenas_sorteio);
	
	
	uint64_t coberturaInicial = computeStartingCoverage(qtd_dezenas_jogo, qtd_dezenas_sorteio, qtd_dez_garante_acertos);
	int combinacaoMenor =comb(qtd_dezenas_sorteio, qtd_dez_garante_acertos);
	int combinacaoCob =comb(qtd_dezenas_jogo, qtd_dezenas_sorteio);
	uint64_t todasGarantia=0;
	uint64_t idxTicket = 0;
	bool estaCoberto = false;
	std::vector<TicketNode> ticket_nodes;
	std::vector<MatchNode> garantias_nodes;
	boost::dynamic_bitset<> combination(qtd_dezenas_jogo);
	std::vector<boost::dynamic_bitset<>> combGarantia;
	std::unordered_map<boost::dynamic_bitset<>, uint64_t> garantias_idx_map;
	//generateCombinations(combination, 0, qtd_dez_garante_acertos,garantias_idx_map,todasGarantia);
	garantias_nodes.resize(combinacaoCob);
	while (tickets.hasNext())
	{
			boost::dynamic_bitset<> ticket = tickets.next();
			//GeraCombIterarBitset combGarantia(qtd_dezenas_jogo,qtd_dez_garante_acertos);
			std::vector<uint32_t> ticketNode;
			//uint64_t idxMatch = 0;
			bool t;
		
			uint64_t idxGaratia = 0;
			for (; ticketsCob.hasNext(); )
			{
				
				//boost::dynamic_bitset<> numBitset = convertNumBitset(combMenor[i],qtd_dezenas_jogo);
				//uint64_t idxGaratia = garantias_idx_map.find(numBitset)->second;
				boost::dynamic_bitset<> ticketCob =ticketsCob.next();
				
				if((ticketCob&ticket).count() == qtd_dez_garante_acertos){
					ticketNode.push_back(idxGaratia);
					garantias_nodes[idxGaratia].ticket_indexes.push_back(idxTicket);
				}
					idxGaratia++;			
			}
			
			// geraCombinacoes( convertBitsetNum(ticket), qtd_dez_garante_acertos,  combMenor);
			
			// for (uint64_t i = 0; i < combMenor.size(); i++)
			// {
			// 	boost::dynamic_bitset<> numBitset = convertNumBitset(combMenor[i],qtd_dezenas_jogo);
			// 	uint64_t idxGaratia = garantias_idx_map.find(numBitset)->second;
			// 	ticketNode.push_back(idxGaratia);
			// 	garantias_nodes[idxGaratia].ticket_indexes.push_back(idxTicket);
								
			// }
			
			ticket_nodes.push_back(TicketNode(estaCoberto, coberturaInicial, ticketNode));
		 ++idxTicket;
			
	}
	garantias_idx_map.clear();
	std::vector<boost::dynamic_bitset<>> allTickets;
	generateCombinations(combination, 0, qtd_dezenas_sorteio,allTickets);

	system("pause");
	std::vector<uint64_t> wheel_ticket_idxs;
	// unordered_map<TicketNode, uint32_t> tentativa_idx_map;
	//  //selecão de indexes

//   // Access the elements in the std::vector
//tentativa_idx_map[tn]=0;
 unsigned long seed1 = std::chrono::system_clock::now().time_since_epoch().count();
     std::mt19937_64 eng(seed1);
     std::uniform_int_distribution<unsigned int> distr(0, ticket_nodes.size()-1);
uint64_t idx_inicial = distr(eng);	 
  
  ticket_nodes[idx_inicial].is_covered=true;
  ticket_nodes[idx_inicial].remaining_coverage=0;
wheel_ticket_idxs.push_back(idx_inicial);
updateSimpleCovered( allTickets,ticket_nodes,wheel_ticket_idxs,qtd_dez_garante_acertos );
updatePotentials(ticket_nodes, garantias_nodes, idx_inicial);
  for (uint64_t i = 0; i < ticket_nodes.size(); i++) {
    // if(tentativa_idx_map[ticket_nodes[i]]==0){
    //        std::cout<<"encontrou o no idx" <<i<<" \n";
    //         system("pause");
    // }
    const TicketNode& tn = ticket_nodes[i];
    std::cout << "idx: " << i << std::endl;
    std::cout << "is_covered: " << tn.is_covered << std::endl;
    std::cout << "remaining_coverage: " << tn.remaining_coverage << std::endl;
    std::cout << "match_indexes: ";
    for (const auto& index : tn.match_indexes) {
      std::cout << index << " ";
    }
    std::cout << std::endl;
  }

  return 0;
}


