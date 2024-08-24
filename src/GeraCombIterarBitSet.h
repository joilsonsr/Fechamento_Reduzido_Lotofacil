/*
 * GeraCombInterar.h
 *
 *  Created on: 17 de dez de 2017
 *      Author: JoilsonDell
 */

#ifndef GERACOMBITERARBITSET_H_
#define GERACOMBITERARBITSET_H_
#include <vector>
#include <boost/dynamic_bitset.hpp>

class GeraCombIterarBitset {
private:
	   std::vector<int> comb;
	    std::vector<int>N ;
	    std::vector<int>entrada ;
	    int numero ;
	    std::vector<int> IndexComb;
	    std::vector<int>k ;
	    bool verdade;
		int d;
	    int l;

public:
	GeraCombIterarBitset(int numeroLoteria,unsigned int numero) {
		d=0;l=0;verdade=true;
		// this->verdade=true;
		if(numero > numeroLoteria)verdade=false;
		this->comb.resize(numero) ;
		this->IndexComb.resize(numeroLoteria) ;
		this->numero = numero ;
		this->N.resize(numero);

		for (int i = 1; i <= numeroLoteria; i++)
		{
			this->entrada.push_back(i);
		}

		for (int k = 0; k < entrada.size(); k++)
			IndexComb[k]=k;
		this->k.resize(numero);
		for (int b = numero-1; b >=0; b--) {

			this->k[b] =this->entrada.size()-d;
			d++;
			// cout<<entrada.size()<<endl;
			//system("Pause");

		}

		for (int k2 = 0; k2 < numero; k2++) {
			this->N[k2]=k2;

		}

	}

	size_t size()
	{

		uint64_t b[entrada.size()+1];

		b[0] = 1;

		for (uint64_t i = 1; i <= entrada.size(); ++i) {
			b[i] = 1;
			for (uint64_t j = i - 1; j > 0; --j) {
			b[j] += b[j-1];
			}
		}

		return b[numero];
	}

	bool hasNext() {
		this->l++;
		//if (l==126)l=2;
		//verdade = true;
		return verdade ;

		}

    boost::dynamic_bitset<> next() {
       	boost::dynamic_bitset<> bs(entrada.size());
	    if(l==1){
		   	for (int j = 0; j < numero; j++) {
	    		this->comb[j] = entrada[N[j]];

	    	}
	       	//cout<<"tamanho N "<<comb[0]<<comb[1]<<comb[2];
	       	for (int var = 0; var < numero; ++var) {
	       		bs.set((comb[var]-1));
	       	}

	    	return bs;

	    }

	    N[numero-1]++;
	       //cout<<N[2]<<endl;

		if(this->N[numero-1]<this->k[numero-1]){
			for (int j = 0; j < numero; j++) {
				comb[j]=this->entrada[N[j]];

			}

			if(N[0]==k[0]-1)this->verdade=false;
			bs.reset();

			for (int var = 0; var < numero; ++var) {
				bs.set((comb[var]-1));
			}
			return bs;

			}else{

				for (int l = (numero-1); l >=0 ; l--) {

					if(N[l]==k[l]){
						N[l-1]+=1;
						N[l]=N[l-1];

					}
				}
		}

	return next();

	}


};
#endif /* GERACOMBITERARBITSET_H_ */

