/*
 * GeraCombInterar.h
 *
 *  Created on: 17 de dez de 2017
 *      Author: JoilsonDell
 */

#ifndef GERACOMBITERAR_H_
#define GERACOMBITERAR_H_
#include <vector>
#include "GeraCombIterar.h"
class GeraCombIterar {
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
	GeraCombIterar(std::vector<int> entrada,int numero) {
	d=0;l=0;verdade=true;
    if(numero >entrada.size())verdade=false;
	   // this->verdade=true;
	
	this->entrada=entrada;this->numero=numero;;
		

   	this->comb.resize(numero) ;
   	this->IndexComb.resize(entrada.size()) ;
   	this->numero = numero ;
       this->N.resize(numero);
       this->entrada = entrada;
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

   };


bool hasNext() {
   	this->l++;
   	//if (l==126)l=2;
   	//verdade = true;
   	return verdade ;

   }

   std::vector<int> next() {
   if(l==1){
   	for (int j = 0; j < numero; j++) {
			this->comb[j] = entrada[N[j]];

		}
   	//cout<<"tamanho N "<<comb[0]<<comb[1]<<comb[2];
   	return comb;

   }

  		N[numero-1]++;
   //cout<<N[2]<<endl;

		if(this->N[numero-1]<this->k[numero-1]){

			for (int j = 0; j < numero; j++) {
				comb[j]=this->entrada[N[j]];

			}


			if(N[0]==k[0]-1)this->verdade=false;
			return comb;

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
#endif /* GERACOMBITERAR_H_ */

