/**
 * Data Structures for
 * Efficient Greedy Lottery Wheel Generator
 *
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
 *
 * See the comments in wheelgen.cc for more information.
 *
 * Last Modified: 11 July 2009
 *
 **/

#ifndef WHEELGEN_H
#define WHEELGEN_H

#include <vector>
#include <sys/types.h>
#include <stdint.h>
//a variavel unsigned is_covered e demais seguidos de dois ponto o numero apos ele é a quantidade maxima de bits aceitavel pela variavel
struct TicketNode
{
  unsigned is_covered         :1;
  unsigned remaining_coverage :31;
  std::vector<uint32_t> match_indexes;
  TicketNode(){}
  TicketNode(bool b_is_covered, int n_remaining_coverage,
             const std::vector<uint32_t>& v_match_indexes)
	: is_covered(b_is_covered),remaining_coverage(n_remaining_coverage), match_indexes(v_match_indexes){}
};

struct MatchNode
{
  	std::vector<uint64_t> ticket_indexes;
	MatchNode(){}
	MatchNode(const std::vector<uint64_t>& v_match_indexes)
	:ticket_indexes(v_match_indexes){}
};

struct DFSStackEntry
{
  unsigned is_ticket    :1;
  unsigned is_level_two :1;
  unsigned is_visited   :1;
  unsigned index        :64;

  DFSStackEntry(uint64_t idx, bool b_is_ticket, bool b_is_level_2)
    : is_ticket(b_is_ticket ? 1 : 0),
      is_level_two(b_is_level_2 ? 1 : 0),
      is_visited(0), index(idx) {}

}
  #ifdef __GNUC__
  __attribute__((packed))
  #endif
  ;

#endif

