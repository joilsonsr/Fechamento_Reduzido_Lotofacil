#include <vector>
#include <sys/types.h>
#include <boost/dynamic_bitset.hpp>
#include "combinacao.h"
using std::vector;

void geraCombinacoes(std::vector<int> entrada, int numero, std::vector<std::vector<int>>& comb){

	// vector<int> entrada;
	// for(int i = 1; i <= numeroComb; i++){
	// 	entrada.push_back(i);
	// }

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


void generateAllCombos(boost::dynamic_bitset<>& combination, int index, int combo_size, std::vector<boost::dynamic_bitset<>>& comb)
{
	if (combo_size == 0)
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
	generateAllCombos(combination, index + 1, combo_size - 1, comb);

	// Do not select the current number
	combination[index] = false;
	generateAllCombos(combination, index + 1, combo_size, comb);
}

/**
 * Computes the binomial coefficient n-choose-k
 * */
size_t comb(size_t n, size_t k)
{
  size_t b[n+1];

  b[0] = 1;

  for (size_t i = 1; i <= n; ++i) {
    b[i] = 1;
    for (size_t j = i - 1; j > 0; --j) {
      b[j] += b[j-1];
    }
  }

  return b[k];
}


/**
 * Computes the starting coverage potential of every ticket. This is equivalent
 * to the number of unique other tickets that share at least one appropriately
 * sized match with any given ticket. This number is the same for all tickets.
 *
 * This particular method of calculation is due to a 2008 paper by Jans &
 * Degraeve in the European Journal of Operational Research:
 * http://ideas.repec.org/a/eee/ejores/v186y2008i1p104-110.html
 **/
size_t computeStartingCoverage(size_t range, size_t ticket_size,
                               size_t match_size)
{ 
  size_t starting_coverage = 0;
  
  for (size_t k = match_size; k < ticket_size; ++k) {
    starting_coverage += comb(ticket_size, k) *
      comb(range - ticket_size, ticket_size - k);
  }

  return starting_coverage;
}