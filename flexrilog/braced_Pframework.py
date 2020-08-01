# -*- coding: utf-8 -*-
r"""
This module implements functionality for investigating braced P-frameworks.


Methods
-------

**Pframework**

{INDEX_OF_METHODS_PFRAMEWORK}


**BracedPframework**

{INDEX_OF_METHODS_BRACEDPFRAMEWORK}

AUTHORS:

-  Jan Legerský (2020-08-01): initial version
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


from .flexible_rigid_graph import FlexRiGraphWithCartesianNACs
from .framework import Framework
from .graph_motion import GraphMotion

class Pframework(FlexRiGraphWithCartesianNACs,Framework):
    """
    This class represents a braced P-framework.

    INPUT:
    - `edges` - edges of a ribbon-cutting graph in a format accepted by :class:`FlexRiGraph`.
    - `placement` - a dictionary with positions of the vertices of the underlying graph.
      The placement must be a parallelogram placement
      of the underlying graph (up to `tolerance`).
    - `check` - if `True` (default), then the underlying graph is checked to be ribbon-cutting and
      the placement to be a parallelogram placement.
    - `tolerance` - numerical tolerance for the check of parallelogram placement.
    - ``allow_adding_parallelograms_and_braces`` - if ``True`` (default), then the framework can be braced 
      (:meth:`add_brace`) and extended by adding parallelograms 
      (:meth:`add_parallelogram` and :meth:`close_parallelogram`).
    """
    def __init__(self, edges, placement, check=True, tolerance=1e-8,
                 allow_adding_parallelograms_and_braces=True, **kwargs):
        super().__init__(edges, placement, check_injectivity=check,
                         tolerance=tolerance, check=check,
                         immutable=not allow_adding_parallelograms_and_braces, **kwargs)
        
        if check:
            if self.triangles():
                raise ValueError(
                    'There are 3-cycles {} which is not possible in a ribbon-cutting graph with a parallelogram placement.'.format(self.unbraced_framework().triangles()))
            for u0,u1,u2,u3 in self.four_cycles():
                if norm(self.placement(u1) - self.placement(u0)
                        - self.placement(u2)+self.placement(u3)) > self._tolerance:
                    raise ValueError(
                        'The placement must be a parallelogram placement: {} is not a parallelogram'.format(
                            (u0,u1,u2,u3)))
            
            rib_cutting, cert = self.is_ribbon_cutting(certificate=True)
            if not rib_cutting:
                raise ValueError('The ribbon {} is not an edge cut.'.format(cert))
                
        self._tikz_vertices = "\\begin{tikzpicture}\n"
        self._latex_vertex_style = 'gvertex'
        for v in self.vertices():
            self._tikz_vertices += "    \\node[" + self._latex_vertex_style + "] ({}) at {} {{}};\n".format(
                v, self.placement(v))
        self._tikz_edges = '    \\draw[edge] ' + ' '.join(
            ["({})--({})".format(u,v) for u,v in self.edges(labels=False)]) + "\n"
        
        self._report('The constructor of Pframework finished')
        
    def _reset(self):
        super()._reset()
        self._diagonals = None
        
    def diagonals(self):
        if not self._diagonals:
            self._diagonals = flatten([[Set([u0,u2]), Set([u1,u3])] 
                                       for u0,u1,u2,u3 in self.four_cycles()],max_level=1)
        return self._diagonals
    
    def coordinates_for_grid_construction(self, delta):
        r"""
        Return coordinates for red and blue components.
        """        
        def get_coordinates(proj):
            root = proj.vertices()[0]
            shortest_paths = proj.shortest_paths(root)
            positions = {root : vector([0,0])}
            shortest_paths
            for v, path in shortest_paths.items():
                if not v in positions:
                    for u,w in zip(path, path[1:]):
                        u_orig, w_orig = proj.edge_label(u,w)
                        if u_orig in w:
                            u_orig, w_orig = w_orig, u_orig
                        if w not in positions:
                            positions[w] = positions[u] + self.placement(w_orig) - self.placement(u_orig)
            return positions
        return {
            'red' : get_coordinates(self.quotient_graph(delta.blue_components(), labeled=True)),
            'blue' : get_coordinates(self.quotient_graph(delta.red_components(), labeled=True))
        }
    
    def flex_from_cartesian_NAC(self, delta):
        coord = self.coordinates_for_grid_construction(delta)
        blue_pos = coord['blue']
        red_pos = coord['red']
        return GraphMotion.GridConstruction(self, delta,
                                            red_components_ordered=[list(comp) for comp in blue_pos.keys()],
                                            blue_components_ordered=[list(comp) for comp in red_pos.keys()],
                                            zigzag=[red_pos.values(), blue_pos.values()])
    

    def add_parallelogram(self, u,v, length=1, alpha_deg=0, new_vertices=None):
        if not self.has_edge(u,v):
            raise ValueError('{} must be an edge.'.format([u,v]))
        alpha = pi*alpha_deg/180
        shift =  matrix([[cos(alpha), -sin(alpha)], [sin(alpha), cos(alpha)]])*vector([length, 0])
        pos_w1 = self.placement(u) + shift
        pos_w2 = self.placement(v) + shift
        
        for i in self.vertices():
            if (norm(self.placement(i) - pos_w1) < self._tolerance
                or norm(self.placement(i) - pos_w2) < self._tolerance):
                raise ValueError('A new vertex coincides with {}'.format(i))

        if type(new_vertices)==list and len(new_vertices)==2:
            w1, w2 = new_vertices
        else:
            max_vert = max(self.vertices())
            w1, w2 = max_vert+1, max_vert+2
        
        self.add_edges([[u,w1], [w1,w2], [w2,v]])
        self._pos[w1] = pos_w1
        self._pos[w2] = pos_w2
        
        self._tikz_vertices += "    \\node[{0},rotate around={1}:({3})] ({4}) at ($({3})+({2:.2f},0)$) {{}};\n".format(
            self._latex_vertex_style, alpha_deg,float(length),u,w1)
        self._tikz_vertices +="    \\node[{}] ({}) at ($({})+({})-({})$) {{}};\n".format(self._latex_vertex_style, w2,w1,v,u)
        self._tikz_edges += "        ({0})--({1}) ({1})--({2}) ({2})--({3})\n".format(u,w1,w2,v)
        
    def close_parallelogram(self, u, v, w, new_vertex=None):
        if not self.has_edge(u,v):
            raise ValueError('{} must be an edge.'.format([u,v]))
        if not self.has_edge(w,v):
            raise ValueError('{} must be an edge.'.format([v,w]))
        if new_vertex==None:
            w_new = max(self.vertices())+1
        else:
            w_new = new_vertex
            
        pos_w_new = self.placement(u) + self.placement(w) - self.placement(v)
        for i in self.vertices():
            if norm(self.placement(i) - pos_w_new) < self._tolerance:
                raise ValueError('The new vertex coincides with {}'.format(i))
                
        self.add_edges([[u,w_new], [w,w_new]])
        self._pos[w_new] = pos_w_new
        self._tikz_vertices +="    \\node[{}] ({}) at ($({})+({})-({})$) {{}};\n".format(self._latex_vertex_style, w_new,u,w,v)
        self._tikz_edges += "        ({0})--({1}) ({1})--({2}) \n".format(u,w_new,w)
    
    def print_tikz_construction(self):
        print(self._tikz_vertices)
        print(self._tikz_edges[:-1]+";\n\\end{tikzpicture}")
        
    def ribbon_graph(self):
        ribbons = self.ribbons()
        V = [tuple(r) for r in ribbons]
        E = []
        for u,v in Subsets(V, 2):
            common = Set([x for e in u for x in e]).intersection(Set([x for e in v for x in e]))
            for par in self.four_cycles():
                if len(Set(par).intersection(common))==4:
                    E.append([u[0], v[0], par])
                    break
        return Graph([[r[0] for r in V],E], format='vertices_and_edges')
    
    def edge2ribbon(self):
        return {e : r[0] 
                for r in self.ribbons()
                for e in r}
    
class BracedPframework(Pframework):
    """
    This class represents a braced P-framework.

    INPUT:
    - `edges` - edges of a ribbon-cutting graph in a format accepted by :class:`FlexRiGraph`.
    - `braces` - a list of pairs of vertices which form diagonals of the ribbon-cutting graph.
    - `placement` - a dictionary with positions of the vertices of the underlying graph.
      The placement must be a parallelogram placement
      of the underlying graph (up to `tolerance`).
    - `check` - if `True` (default), then the underlying graph is checked to be ribbon-cutting and
      the placement to be a parallelogram placement.
    - `tolerance` - numerical tolerance for the check of parallelogram placement.
    """
    def __init__(self, edges, placement, braces=[], check=True, tolerance=1e-8, **kwargs):
        unbraced_framework = Pframework(edges, placement)
        parallelograms = unbraced_framework.four_cycles()
        diagonals = flatten([[Set([u0,u2]), Set([u1,u3])] 
                                   for u0,u1,u2,u3 in parallelograms],max_level=1)
        for brace in braces:
            if not Set(brace) in diagonals:
                raise ValueError(str(brace) + ' is not a diagonal of a 4-cycle of the underlying graph.')
    
        self._braces = [Set(e) for e in braces]
        
        super().__init__(unbraced_framework.edges(labels=False)+braces, 
                         placement, check=False, tolerance=tolerance,  **kwargs)
        self._check = check
        
        self._report('The constructor of BracedPframework finished')

    def _reset(self):
        super()._reset()
        self._unbraced_framework = None
        
    def add_brace(self, u,v=None):
        if v==None:
            e = Set(u)
        else:
            e = Set([u,v])
        if not e in self.unbraced_framework().diagonals():
            raise ValueError('{} must be a diagonal of a parallelogram.'.format(e))
        self.add_edge(e)
        self._braces.append(e)
    
    def add_braces(self, braces):
        for e in braces:
            if not Set(e) in self.unbraced_framework().diagonals():
                raise ValueError('{} must be a diagonal of a parallelogram.'.format(e))
        self.add_edges(braces)
        self._braces += [Set(e) for e in braces]
        
    def unbraced_framework(self):
        if self._unbraced_framework==None:
            self._unbraced_framework = Pframework([e for e in self.edges(labels=False)
                                                   if not Set(e) in self._braces],
                                                  self.placement())
        return self._unbraced_framework
        
    def parallelograms(self):
        return self.unbraced_framework().four_cycles()
    
    def print_tikz_construction(self):
        print(self._tikz_vertices)
        print('    \\draw[brace] ' + ' '.join(
            ["({})--({})".format(u,v) for u,v in self._braces]) + ";\n")
        print(self._tikz_edges[:-1]+";\n\\end{tikzpicture}")
        
    def ribbons(self):
        res = []
        for ribbon in self.unbraced_framework().ribbons():
            verts = [v for e in ribbon for v in e]
            for brace in self._braces:
                if brace[0] in verts and brace[1] in verts:
                    ribbon.append(brace)
            res.append(ribbon)
        return res
    
    def ribbon_graph(self):
        return self.unbraced_framework().ribbon_graph()
    
    def plot(self, **kwargs):
        """
        Return the plot of the braced framework.
        """
        return super().plot(edge_colors={'lightgrey':self._braces}, **kwargs)
    
    def bracing_graph(self):
        ribbons = self.ribbons()
        return Graph([[r[0] for r in ribbons],
                       [[ribbon[0] for ribbon in ribbons if brace in ribbon]
                       for brace in self._braces]
                      ], format='vertices_and_edges')


   

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_PFRAMEWORK}", (gen_thematic_rest_table_index(Pframework)
   )).replace(
    "{INDEX_OF_METHODS_BRACEDPFRAMEWORK}", (gen_thematic_rest_table_index(BracedPframework)
   ))



















