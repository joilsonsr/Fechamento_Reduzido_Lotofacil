#ifndef COMBINACAO_H
#define COMBINACAO_H

#include <vector>
#include <stdint.h>
#include <sys/types.h>
#include <boost/dynamic_bitset.hpp>

void geraCombinacoes(std::vector<int> entrada, int numero, std::vector<std::vector<int>>& comb);
void generateAllCombos(boost::dynamic_bitset<>& combination, int index, int combo_size, std::vector<boost::dynamic_bitset<>>& comb);

size_t computeStartingCoverage(size_t range, size_t ticket_size,
                               size_t match_size);

size_t comb(size_t n, size_t k);

#endif
