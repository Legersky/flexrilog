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

from sage.all import Graph, Set#, show
from sage.all import SageObject, latex, flatten
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.misc.latex import latex_variable_name
from sage.all import PermutationGroup
from sage.all import copy

from .NAC_coloring import NACcoloring


class CnSymmetricNACcoloring(NACcoloring):
    r"""
    The class for a $\\mathcal{C}_n$-symmetric NAC-coloring of a $\\mathcal{C}_n$-symmetric graph.

    We define a NAC-coloring $\\delta$ to be a $\\mathcal{C}_n$-symmetric if
    
    - $\\delta(\\omega e)$ = $\\delta(e)$ for all $e \in E_G$, where $\\omega$ generates $\\mathcal{C}_n$, and 
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



__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(CnSymmetricNACcoloring)))
