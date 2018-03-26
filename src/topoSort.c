/**
   Topological sorting.
 */

#include <stdlib.h>
#include <string.h>
#include "graph.h"
 
/* Find out if a vertex has no incoming arcs, 
   or if the vertex is not in the graph. */
static unsigned int is_root_or_absent(const arc *graph,
				      const unsigned char *validArcs, // booleans for lookups in graph
				      unsigned int size, // of validArcs and graph
				      unsigned int vertex)
{
  for (unsigned int a = 0; a < size; a++)
    if (validArcs[a] && graph[a].second == vertex)
      return 0;
  return 1;
}
 
/* Get a vertex with no incoming arcs and with label < order. */
static unsigned int find_root(const arc *graph,
			      const unsigned char *validVertices,
			      const unsigned char *validArcs, // booleans for lookups in graph
			      unsigned int size, // of validArcs and graph
			      unsigned int order)
{
  for (unsigned int v = 0; v < order; v++)
    {
      if (validVertices[v] && is_root_or_absent(graph, validArcs, size, v))
	return v; // a valid vertex is not absent
    }
  return -1; // no root with label < order
}

/**
   Sort a graph with vertices labelled from 0 to order-1.
   A finite graph with other kinds of label can be numbered like this.
 */
unsigned char topological_sort(const arc *graph,
			       unsigned int size, // number of arcs in the graph
			       unsigned int order,
			       /*out*/unsigned int *sorted)
{
  unsigned char *validArcs = malloc(size * sizeof(unsigned char)); // booleans
  unsigned char *validVertices = malloc(order * sizeof(unsigned char)); // booleans
  unsigned int sorted_size = 0;
  if (!validArcs || !validVertices)
    {
      free(validVertices);
      free(validArcs);
      return 0;
    }
  
  /* All vertices and arcs start off in the graph */
  memset(/*out*/validVertices, 1, order * sizeof(unsigned char));
  memset(/*out*/validArcs, 1, size * sizeof(unsigned char));
    
  while (sorted_size < order)
    {
      const unsigned int v = find_root(graph, validVertices, validArcs, size, order);
      if (v == -1)
	{
	  /* The graph has no roots, so it has a cycle.
	     Proof: we pick a vertex and follow the arcs backwards from it.
	     Because the graph has no roots, the backward path never stops
	     and we follow it order+1 steps. Some vertex was visited twice. */
	  break;
	}

      // Append root v to sorted
      validVertices[v] = 0;
      sorted[sorted_size++] = v;
      
      /* Remove all arcs starting from v */
      for (unsigned int a = 0; a < size; a++)
	if (graph[a].first == v)
	  validArcs[a] = 0;
    }
  free(validVertices);
  free(validArcs);
  return sorted_size == order;
}
