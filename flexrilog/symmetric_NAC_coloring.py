# -*- coding: utf-8 -*-
r"""
This class implements NAC-colorings of graphs with a symmetry.

$\\mathcal{C}_n$-symmetric NAC-coloring
---------------------------------------

{INDEX_OF_METHODS_CN}


$\\mathcal{C}_s$-symmetric NAC-coloring
---------------------------------------

{INDEX_OF_METHODS_CS}

AUTHORS:

-  Jan Legerský (2020-03-12): initial version
-  Jan Legerský (2022-05-19): Cs-symmetry added

CnSymmetricNACcoloring
----------------------
"""

#Copyright (C) 2018 Jan Legerský
#
#This program is free software: you can redistribute it and/or modify
#it under the terms of the GNU General Public License as published by
#the Free Software Foundation, either version 3 of the License, or
#(at your option) any later version.
#
#This program is distributed in the hope that it will be useful,
#but WITHOUT ANY WARRANTY; without even the implied warranty of
#MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License
#along with this program.  If not, see <https://www.gnu.org/licenses/>.

from sage.all import Graph, Set, Subsets#, show
from sage.all import SageObject, latex, flatten
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.misc.latex import latex_variable_name
from sage.all import PermutationGroup
from sage.all import copy

from .NAC_coloring import NACcoloring
from .flexible_rigid_graph import FlexRiGraph


class CnSymmetricNACcoloring(NACcoloring):
    r"""
    The class for a $\\mathcal{C}_n$-symmetric NAC-coloring of a $\\mathcal{C}_n$-symmetric graph.

    We define a NAC-coloring $\\delta$ to be a $\\mathcal{C}_n$-symmetric if
    
    - $\\delta(\\omega e)$ = $\\delta(e)$ for all $e \\in E_G$, where $\\omega$ generates $\\mathcal{C}_n$, and 
    - no two distinct blue, resp. red, partially invariant components are connected by an edge.
    """
    def __init__(self, G, coloring, name=None, check=True):
        from .symmetric_flexible_rigid_graph import CnSymmetricFlexRiGraph
        if not isinstance(G, CnSymmetricFlexRiGraph):
            raise ValueError('The graph G must be an instance of CnSymmetricFlexRiGraph.')
        super(CnSymmetricNACcoloring, self).__init__(G, coloring, name, check)
        self.n = self._graph.n
        self.omega = self._graph.omega
        self._find_components_orbits()
        if check and not self.is_Cn_symmetric():
            raise ValueError('The coloring is not a Cn-symmetric NAC-coloring.')
        
    
    def _find_components_orbits(self):
        red_subgraph = self.red_subgraph()
        blue_subgraph = self.blue_subgraph()
        self._partially_invariant_components = {}
        self._noninvariant_components = {}
        self._partially_invariant_orbits = {}
        self._noninvariant_orbits = {}
        for one_color_subgraph,  col in [[red_subgraph, 'red'],
                                         [blue_subgraph, 'blue']]:
            invariant_comps = []
            noninv_comps = []
            comps_as_sets = [Set(component) for component in one_color_subgraph.connected_components()]
            comps_perm = PermutationGroup([[Set([self.omega(v) for v in component]) for component in comps_as_sets]],
                                         domain=comps_as_sets)
            for orbit in comps_perm.orbits():
                if len(orbit)<self.n:
                    invariant_comps.append(orbit)
                else:
                    noninv_comps.append(orbit)
                    
            self._partially_invariant_orbits[col] = invariant_comps
            self._noninvariant_orbits[col] = noninv_comps
            self._partially_invariant_components[col] = [list(comp) for orbit in invariant_comps for comp in orbit]
            self._noninvariant_components[col] = [list(comp) for orbit in noninv_comps for comp in orbit]
    
    def is_Cn_symmetric(self):
        if not self.is_equal(self.isomorphic_NAC_coloring(self.omega), moduloConjugation=False):
            return False
        if self.blue_subgraph(
            ).subgraph(flatten(self._partially_invariant_components['red'], max_level=1)).num_edges()>0:
            return False
        if self.red_subgraph(
            ).subgraph(flatten(self._partially_invariant_components['blue'], max_level=1)).num_edges()>0:
            return False
        return True

    def _repr_(self):
        """
        Return a string representation of `self`.
        
        Extend the string representation of NACcoloring.
        """
        return NACcoloring._repr_(self).replace('NAC', 'Cn-symmetric NAC')

    def partially_inv_components_connected(self):
        r"""
        Return whether some partially invariant components of the same color are connected by a path.
        
        EXAMPLE::
        
            sage: from flexrilog import FlexRiGraph, CnSymmetricFlexRiGraph
            sage: G = FlexRiGraph([(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
            ....:                      (4,5), (4,6), (4,7), (5,6), (5,7), (6,7),
            ....:                      (0,8), (1,9), (2,10),
            ....:                      (4,8), (5,9), (6,10), 
            ....:                     ])
            sage: Gsym = CnSymmetricFlexRiGraph(G, CnSymmetricFlexRiGraph.Cn_symmetries_gens(G, 3)[0])
            sage: [[cls[0], cls[0].partially_inv_components_connected()]
            ....:         for cls in Gsym.NAC_colorings_isomorphism_classes()]
            [[Cn-symmetric NAC-coloring with 12 red edges and 6 blue edges , True],
             [Cn-symmetric NAC-coloring with 9 red edges and 9 blue edges , True],
             [Cn-symmetric NAC-coloring with 9 red edges and 9 blue edges , False]]
             
        The $\\mathcal{C}_3$-symetric NAC-colorings in the example above are the following:
        
        .. PLOT::
        
            from flexrilog import FlexRiGraph, CnSymmetricFlexRiGraph
            G = FlexRiGraph([(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
                    (4,5), (4,6), (4,7), (5,6), (5,7), (6,7),
                    (0,8), (1,9), (2,10),
                    (4,8), (5,9), (6,10), ])
            Gsym = CnSymmetricFlexRiGraph(G, CnSymmetricFlexRiGraph.Cn_symmetries_gens(G, 3)[0],
                    pos={0: (1.324, 0.579), 4: (1.322, -0.640), 8: (1.645, -0.039), 3: (0, -0.1), 7: (0, 0.1)})
            sphinx_plot(graphics_array([cls[0].plot() for cls in Gsym.NAC_colorings_isomorphism_classes()]))
        """
        quotient_by_blue = FlexRiGraph(self.red_subgraph(), check=False
                                      ).quotient_graph(self._partially_invariant_components['blue'])
        quotient_by_red = FlexRiGraph(self.blue_subgraph(), check=False
                                     ).quotient_graph(self._partially_invariant_components['red'])
        for u,v in Subsets([Set(comp) for comp in self._partially_invariant_components['blue']], 2):
            if quotient_by_blue.shortest_path(u, v):
                return True
        for u,v in Subsets([Set(comp) for comp in self._partially_invariant_components['red']], 2):
            if quotient_by_red.shortest_path(u, v):
                return True
        return False
    
    def vertices_in_blue_and_red_partially_inv_components(self):
        r"""
        Return the vertices that are simultaneously in a red and blue partially invariant component.
                
        EXAMPLE::
                
            sage: from flexrilog import FlexRiGraph, CnSymmetricFlexRiGraph
            sage: G = FlexRiGraph([(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
            ....:                      (4,5), (4,6), (4,7), (5,6), (5,7), (6,7),
            ....:                      (0,8), (1,9), (2,10),
            ....:                      (4,8), (5,9), (6,10), 
            ....:                     ])
            sage: Gsym = CnSymmetricFlexRiGraph(G, CnSymmetricFlexRiGraph.Cn_symmetries_gens(G, 3)[0])
            sage: [[cls[0], cls[0].vertices_in_blue_and_red_partially_inv_components()]
            ....:         for cls in Gsym.NAC_colorings_isomorphism_classes()]
                [[Cn-symmetric NAC-coloring with 12 red edges and 6 blue edges , [3, 7]],
                 [Cn-symmetric NAC-coloring with 9 red edges and 9 blue edges ,
                  [3, 8, 9, 10, 7]],
                 [Cn-symmetric NAC-coloring with 9 red edges and 9 blue edges , [3, 7]]]
        
        The $\\mathcal{C}_3$-symetric NAC-colorings in the example above are the following:
        
        .. PLOT::
        
            from flexrilog import FlexRiGraph, CnSymmetricFlexRiGraph
            G = FlexRiGraph([(0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
                    (4,5), (4,6), (4,7), (5,6), (5,7), (6,7),
                    (0,8), (1,9), (2,10),
                    (4,8), (5,9), (6,10), ])
            Gsym = CnSymmetricFlexRiGraph(G, CnSymmetricFlexRiGraph.Cn_symmetries_gens(G, 3)[0],
                    pos={0: (1.324, 0.579), 4: (1.322, -0.640), 8: (1.645, -0.039), 3: (0, -0.1), 7: (0, 0.1)})
            sphinx_plot(graphics_array([cls[0].plot() for cls in Gsym.NAC_colorings_isomorphism_classes()]))
        """
        blue = flatten(self._partially_invariant_components['blue'], max_level=1)
        return [v for v in flatten(self._partially_invariant_components['red'], max_level=1)
                if v in blue]
        
    def grid_construction_is_injective(self):
        r"""
        Return if the Cn-symmetric grid construction has injective placements.
        
        This is the case if:
        
         - each red component intersects with each blue component in at most one vertex 
           (:meth:`flexrilog.NAC_coloring.NACcoloring.grid_coordinates_are_injective`),
         - no two blue, resp. red, partially invariant components are connected 
           by a red, resp. blue, path (:meth:`partially_inv_components_connected`), and 
         - at most one vertex is in a blue and red partially invariant component simultaneously
           (:meth:`vertices_in_blue_and_red_partially_inv_components`). 
          
        """
        if (self.grid_coordinates_are_injective()
            and not self.partially_inv_components_connected()
            and len(self.vertices_in_blue_and_red_partially_inv_components())<=1):
            return True
        else:
            return False

class CsSymmetricNACcoloring(NACcoloring):
    r"""
    The class for a $\\mathcal{C}_s$-symmetric NAC-coloring of a $\\mathcal{C}_s$-symmetric graph.

    We define a NAC-coloring $\\delta$ to be a $\\mathcal{C}_s$-symmetric if
    
    - $\\delta(\\sigma e)$ is red iff  $\\delta(e)$ is blue for all $e \\in E_G$,
      where $\\sigma$ generates $\\mathcal{C}_s$, and 
    - If $\\delta(e)$ is golden then $\\delta(\\sigma e)$ is golden.
    """
    def __init__(self, G, coloring, name=None, check=True):
        if type(G) == FlexRiGraph or 'FlexRiGraph' in str(type(G)) or isinstance(G, FlexRiGraph):
            self._graph = G
        else:
            raise TypeError('The graph G must be FlexRiGraph.')
        from .symmetric_flexible_rigid_graph import CsSymmetricFlexRiGraph
        if check and not isinstance(G, CsSymmetricFlexRiGraph):
            raise ValueError('The graph G must be an instance of CsSymmetricFlexRiGraph.')
            
            
        if type(coloring) in [list, Set] and len(coloring) == 3:
            self._red_edges = Set([Set(e) for e in coloring[0]])
            self._blue_edges = Set([Set(e) for e in coloring[1]])
            self._golden_edges = Set([Set(e) for e in coloring[2]])
        elif type(coloring) == dict:
            self._red_edges = Set([Set(e) for e in coloring if coloring[e] == 'red'])
            self._blue_edges = Set([Set(e) for e in coloring if coloring[e] == 'blue'])
            self._golden_edges = Set([Set(e) for e in coloring if coloring[e] == 'golden'])
        elif (type(coloring)==CsSymmetricNACcoloring 
              or isinstance(coloring, CsSymmetricNACcoloring)):
            self._red_edges = copy(coloring._red_edges)
            self._blue_edges = copy(coloring._blue_edges)
            self._golden_edges = copy(coloring._golden_edges)
        else:
            raise TypeError('The coloring must be a dict, list consisting of three lists or an instance of Cs-NACcoloring.')
        self._name = name
        self.sigma = self._graph.sigma
        if check:
            self._check_edges()
            if not self.is_Cs_symmetric():
                raise ValueError('The coloring is not a Cs-symmetric NAC-coloring.')
          
    def is_Cs_symmetric(self):
        if not self.is_equal(self.isomorphic_NAC_coloring().conjugated(), moduloConjugation=False):
            return False
        if (not NACcoloring(self._graph, [self.red_edges(), self.blue_edges()+self.golden_edges()],
                            check=False).is_NAC_coloring()
            or not NACcoloring(self._graph, [self.red_edges()+self.golden_edges(), self.blue_edges()],
                               check=False).is_NAC_coloring()):
            return False
        return True


    def _repr_(self):
        """
        Return a string representation of `self`.
        """
        res = (self._name + ': ') if self._name != None else ''
        res += 'Cs-symmetric NAC-coloring with '
        if self._graph.num_edges()< 10:
            res += 'red edges ' + str(sorted([sorted(list(e)) for e in self._red_edges]))
            res += ', blue edges ' + str(sorted([sorted(list(e)) for e in self._blue_edges]))
            res += ' and golden edges ' + str(sorted([sorted(list(e)) for e in self._golden_edges]))
        else:
            res += str(len(self._red_edges)) + ' red edges, '
            res += str(len(self._blue_edges)) + ' blue edges and '
            res += str(len(self._golden_edges)) + ' golden edges'
        return res

    
    def _latex_(self):
        if self._name:
            l_name = latex_variable_name(self._name) + ': \\left( \\{'
        else:
            l_name = '\\left( \\{'
        return (l_name +','.join(['\\{' + latex(u) +','+ latex(v) + '\\}' 
                            for u,v in sorted([sorted(list(e)) for e in self._red_edges])])
                        + r'\} \mapsto red; \{'
                        + ','.join(['\\{' + latex(u) +','+ latex(v) + '\\}' 
                            for u,v in sorted([sorted(list(e)) for e in self._blue_edges])])
                        + r'\} \mapsto blue; \{'
                        + ','.join(['\\{' + latex(u) +','+ latex(v) + '\\}' 
                            for u,v in sorted([sorted(list(e)) for e in self._golden_edges])])
                        + r'\} \mapsto golden\right)')
    

    def _check_edges(self):
        r"""
        Raise a ``RuntimeError`` if the edges of the NAC-coloring do not match the edges of the graph.
        """
        if len(self._blue_edges) + len(self._red_edges) + len(self._golden_edges) != self._graph.num_edges():
            raise RuntimeError('The edges of the NAC-coloring do not match the edges of the graph.')
        if (Set([Set(e) for e in self._graph.edges(labels=False, sort=False)])
            != self._blue_edges.union(self._red_edges).union(self._golden_edges)):
            raise RuntimeError('The edges of the NAC-coloring do not match the edges of the graph.')
    
    def golden_edges(self):
        r"""
        Return the list of golden edges of the NAC-coloring.
        """
        return list(self._golden_edges)
    

    def color(self, u, v=None):
        r"""
        Return the color of an edge.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.
        """
        if not v is None:
            if not self._graph.has_edge(u,v):
                raise ValueError('There is no edge ' + str([u,v]))
            e = Set([u,v])
            if e in self._golden_edges:
                return 'golden'
            elif e in self._blue_edges:
                return 'blue'
            else:
                return 'red'
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise ValueError('There is no edge ' + str([u[0],u[1]]))
            e = Set([u[0],u[1]])
            if e in self._golden_edges:
                return 'golden'
            elif e in self._blue_edges:
                return 'blue'
            else:
                return 'red'
            

    def is_golden(self, u, v=None):
        r"""
        Return if the edge is golden.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.
        """
        if not v is None:
            if not self._graph.has_edge(u,v):
                raise ValueError('There is no edge ' + str([u,v]))
            return Set([u,v]) in self._golden_edges
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise ValueError('There is no edge ' + str([u[0],u[1]]))
            return Set([u[0],u[1]]) in self._golden_edges
        
    def golden_subgraph(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._golden_edges]], format='vertices_and_edges')


    def golden_components(self):
        return self.golden_subgraph().connected_components()
    
   
    def red_blue_components(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._red_edges + self._blue_edges]], 
                     format='vertices_and_edges').connected_components()    
   
    def red_golden_components(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._red_edges + self._golden_edges]], 
                     format='vertices_and_edges').connected_components()    
   
    def blue_golden_components(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._golden_edges + self._blue_edges]], 
                     format='vertices_and_edges').connected_components()
                     
    
    def plot(self, grid_pos=False, zigzag=False, **args_kwd):
        r"""
        Return a plot of the NAC-coloring.
        """
        if self.name():
            args_kwd['title'] = '$'+latex_variable_name(self.name())+'$'

        from .__init__ import colB, colR, colG
        edge_colors = {
                colB : self.blue_edges(),
                colR : self.red_edges(),
                colG : self.golden_edges()
                }
        return self._graph.plot(edge_colors=edge_colors, name_in_title=False, **args_kwd)

    def path_is_unicolor(self, path):
        r"""
        Return if the edges of the path have the same color.
        """
        edges = Set([Set(e) for e in zip(path[:-1],path[1:])])
        return edges.issubset(self._red_edges) or edges.issubset(self._blue_edges) or edges.issubset(self._golden_edges)
    
    def conjugated(self):
        r"""
        Return the conjugated NAC-coloring.
        """
        return CsSymmetricNACcoloring(self._graph, [self.blue_edges(), self.red_edges(), self.golden_edges()], check=False)


    def print_tikz(self, **kwargs):
        r"""
        Print TikZ code for the graph colored with the NAC-coloring.
        """
        self._graph.print_tikz([self.blue_edges(), self.red_edges(), self.golden_edges()], ['redge', 'bedge', 'gedge'], **kwargs)
        

    def isomorphic_NAC_coloring(self, onlySets=False):
        r"""
        Return the Cs-NAC-coloring under the morphism ``sigma``.
        """
        if onlySets:
            return [Set([Set([self.sigma(e[0]),self.sigma(e[1])]) for e in self._red_edges]),
                    Set([Set([self.sigma(e[0]),self.sigma(e[1])]) for e in self._blue_edges]),
                    Set([Set([self.sigma(e[0]),self.sigma(e[1])]) for e in self._golden_edges])]
        else:
            return CsSymmetricNACcoloring(self._graph, 
                                 [[[self.sigma(e[0]),self.sigma(e[1])] for e in edges] 
                                  for edges in [self._red_edges, self._blue_edges, self._golden_edges]], check=False)

    def has_almost_red_blue_cycle(self, certificate=False):
        if len(self._golden_edges) == 0:
            return (False, None) if certificate else False 
        v2c = {}
        cnt = 0
        red_blue_subgraph = self.red_subgraph().union(self.blue_subgraph())
        for component in red_blue_subgraph.connected_components():
            for v in component:
                v2c[v] = cnt
            cnt +=1
        for u,v in self._golden_edges:
            if v2c[v]==v2c[u]:
                return (True, red_blue_subgraph.shortest_path(u,v)) if certificate else True
    
        return (False, None) if certificate else False 

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_CN}", (gen_rest_table_index(CnSymmetricNACcoloring)))


__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_CS}", (gen_rest_table_index(CsSymmetricNACcoloring)))



