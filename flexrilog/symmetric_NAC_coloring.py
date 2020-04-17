# -*- coding: utf-8 -*-
r"""
This class implements a NAC-coloring of a graph with a symmetry.

Methods
-------


{INDEX_OF_METHODS}

AUTHORS:

-  Jan Legerský (2020-03-12): initial version

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
        if len(self.blue_subgraph().subgraph(flatten(self._partially_invariant_components['red'])).edges())>0:
            return False
        if len(self.red_subgraph().subgraph(flatten(self._partially_invariant_components['blue'])).edges())>0:
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
        blue = flatten(self._partially_invariant_components['blue'])
        return [v for v in flatten(self._partially_invariant_components['red'])
                if v in blue]

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(CnSymmetricNACcoloring)))
