# -*- coding: utf-8 -*-
r"""
This module implements functionality for investigating frameworks.


Methods
-------

**Framework**

{INDEX_OF_METHODS_FRAMEWORK}

AUTHORS:

-  Jan Legerský (2020-08-01): initial version

Framework
-----------

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

#from sage.all_cmdline import *   # import sage library
from sage.all import Graph, Set, ceil, sqrt, matrix, deepcopy, copy
from sage.all import Subsets, rainbow, show, binomial, RealField, flatten
from sage.all import var, solve, RR, vector, norm, CC
from sage.all import PermutationGroup, PermutationGroup_generic
from sage.all import pi, cos, sin
import random
from itertools import chain

from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
from sage.rings.integer import Integer


from .NAC_coloring import NACcoloring
from .flexible_rigid_graph import FlexRiGraph

class Framework(FlexRiGraph):
    """
    This class represents a framework, i.e., a graph with its placement.

    INPUT:
    - `edges` - edges of a graph in a format accepted by :class:`FlexRiGraph`.
    - `placement` - a dictionary with positions of the vertices of the underlying graph.
    - `check_injectivity` - if `True`, then the placement is checked to be injective.
    - `tolerance` - numerical tolerance for the injectivity check.
    """    
    def __init__(self, edges, placement, check_injectivity=False, tolerance=1e-8, **kwargs):
        super().__init__(data=edges, pos=placement,  **kwargs)
        self._tolerance = tolerance
        if check_injectivity:
            inj, cert = self.is_injective(certificate=True)
            if not inj:
                raise ValueError(
                        'The placement is not injective: {} and {} are mapped to the same point'.format(*cert))
        self._vertex_color = 'white'
        self._report('The constructor of Framework finished')
        
    def is_injective(self, certificate=False):
        positions = [self.placementRR(u) for u in self.vertices()]
        for u,v in Subsets(range(len(positions)),2):
            if norm(positions[u] - positions[v]) < self._tolerance:
                return [False, [u,v]] if certificate else False 
        return [True, None] if certificate else True
    
    def placement(self, v=None):
        """
        Return the position of `v` or the placement if `v` is `None`.
        """
        if v != None:
            return vector(self._pos[v])
        else:
            return {v:vector(p) for v,p in self._pos.items()}
    
    def placementRR(self, v):
        """
        Return the position of `v` converted to RealField.
        """
        return vector([RR(self._pos[v][0]), RR(self._pos[v][1])])
        
    def _repr_(self):
        return self.__class__.__name__ + " consisting of " + super(
            )._repr_().replace(self.__class__.__name__,self.__class__.__bases__[0].__name__) + " and its placement"

   

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_FRAMEWORK}", (gen_thematic_rest_table_index(Framework)
   ))



















