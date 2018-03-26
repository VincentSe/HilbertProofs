/**
   The graph's nodes are numbers. An arc first=2, second=7 in a graph means that
   - there is a vertex labelled 2 in the graph
   - there is a vertex labelled 7 in the graph
   - there is an arc starting from vertex 2 and ending at vertex 7
 */
typedef struct
{
  unsigned int first;
  unsigned int second;
} arc;

unsigned char topological_sort(const arc *graph,
			       unsigned int size, // number of arcs in the graph
			       unsigned int order, // number of vertices in the graph
			       /*out*/unsigned int *sorted);
