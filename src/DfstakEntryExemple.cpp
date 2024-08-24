#include<iostream>
#include <stack>
#include <cstdint>
#include "combinacao.h"
#include "wheelgen.h"

int main() {
	size_t garantiaNode_idx_max = comb(15,14);
	std::cout<<garantiaNode_idx_max<<" \n";
	system("pause");
  std::stack<DFSStackEntry> dfs_stack;

  // Push some DFSStackEntry elements onto the stack
  // Coloca alguns elementos DFSStackEntry na pilha
  dfs_stack.push(DFSStackEntry(1, true, false));
  dfs_stack.push(DFSStackEntry(2, false, true));
  dfs_stack.push(DFSStackEntry(3, true, false));

  // Print the top element's index value
  // Imprime o valor do índice do elemento superior
  std::cout << dfs_stack.top().index << " topo "<<std::endl;  // prints 3

  // Pop the top element
  //retira o elemento
  dfs_stack.pop();

  // Print the top element's index value again
  // Imprime o valor do índice do elemento superior novamente
  std::cout << dfs_stack.top().index << std::endl;  // prints 2

  return 0;
}
