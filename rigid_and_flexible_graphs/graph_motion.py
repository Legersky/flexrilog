# -*- coding: utf-8 -*-
r"""
This is implementation of motions of a graph.

Methods
-------


{INDEX_OF_METHODS}

AUTHORS:

-  Jan Legerský (2019-01-24): initial version

Class
-------
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

from sage.all import deepcopy, Set#, Graph, ceil, sqrt, matrix, copy
from sage.all import SageObject #, Subsets, rainbow, latex, flatten
from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
from sage.rings.rational import Rational
from rigid_flexible_graph import RigidFlexibleGraph
import exceptions


class GraphMotion(SageObject):
    r"""
    
    """
    def __init__(self, graph, input_format, active_NACs, data=None,  check=True):
        r"""
        
        """
        self._graph = graph
        self._parameter = None
        self._is_parametric = None
        self._par_type = 'symbolic'
        self._field = None
        if input_format == "grid":
            self._grid2motion(active_NACs[0], data,  check)
    
    
    def _grid2motion(self, NAC_coloring, zigzag, check):
        self._is_parametric = True
        self._par_type = 'symbolic'
        alpha = var('alpha')
        self._parameter = alpha
        grid_coor = NAC_coloring.grid_coordinates()
        if check and len(Set(grid_coor.values())) != self._graph.num_verts():
            raise exceptions.ValueError('The NAC-coloring does not yield a proper flexible labeling.')
        if zigzag:
            if type(zigzag) == list and len(zigzag) == 2:
                a = [vector(c) for c in zigzag[0]]
                b = [vector(c) for c in zigzag[1]]
            else:
                m = max([k for _, k in grid_coor.values()])
                n = max([k for k, _ in grid_coor.values()])
                a = [vector([0.3*((-1)^i-1)+0.3*sin(i), i]) for i in range(0,m+1)]
                b = [vector([j, 0.3*((-1)^j-1)+0.3*sin(j)]) for j in range(0,n+1)]
        else:
            positions = {}
            m = max([k for _, k in grid_coor.values()])
            n = max([k for k, _ in grid_coor.values()])
            a = [vector([0, i]) for i in range(0,m+1)]
            b = [vector([j, 0]) for j in range(0,n+1)]

        rotation = matrix([[cos(alpha), sin(alpha)], [-sin(alpha), cos(alpha)]])
        positions = {}
        for v in self._graph.vertices():
            positions[v] = rotation * a[grid_coor[v][1]] + b[grid_coor[v][0]]
        self._parametrization = positions


    def parametrization(self):
        r"""
        Return the parametrization.
        """
        if self._is_parametric:
            return deepcopy(self._parametrization)
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def realization(self, value,  numeric=False):
        r"""
        Return the realization for given value of the parameter.
        """
        if self._is_parametric:
            res = {}            
            if self._par_type == 'symbolic':
                subs_dict = { self._parameter : value}
                for v in self._parametrization:
                    if numeric:
                        res[v] = vector([RR(xi.subs(subs_dict)) for xi in self._parametrization[v]])
                    else:
                        res[v] = vector([xi.subs(subs_dict) for xi in self._parametrization[v]])
                return res
            else:
                exceptions.NotImplementedError('')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def sample_parametrization(self, N,  type,  interval=None):
        r"""
        Return the realization for given value of the parameter.
        """
        if self._is_parametric:
            if interval == None:
                a = -pi
                b = pi
            if type == 'uniform':
                return [self.realization(RR(a + (i/Integer(N)) * (b-a)),  numeric=True) for i in range(0, N+1)]
            elif type == 'tan':
                return [self.realization(tan(RR(a + (i/Integer(N)) * (b-a))/2.0),  numeric=True) for i in range(0, N+1)]
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    @staticmethod
    def GridConstruction(graph,  NAC_coloring,  zigzag=False):
        return GraphMotion(graph, 'grid',  [NAC_coloring],  data=zigzag)


    def _minmax_xy(self, embeddings, rel_margin):
        max_x ,max_y, min_x, min_y = (0,0,0,0)
        for embd in embeddings:
            for v in embd:
                max_x = max(max_x, embd[v][0])
                max_y = max(max_y, embd[v][1])
                min_x = min(min_x, embd[v][0])
                min_y = min(min_y, embd[v][1])

        max_x = max_x+rel_margin*(max_x-min_x)
        max_y = max_y+rel_margin*(max_y-min_y)
        min_x = min_x-rel_margin*(max_x-min_x)
        min_y = min_y-rel_margin*(max_y-min_y)
        return min_x,  max_x,  min_y,  max_y
    
    def _shift_scale_fun(self,  embeddings,  rel_margin, width):
        min_x,  max_x,  min_y,  max_y = self._minmax_xy(embeddings,  rel_margin)
        size_x = max_x-min_x
        size_y = max_y-min_y

        if size_x>size_y:
            def shift_scale(xy):
                x, y = xy
                return [float((x-min_x)*width/size_x), float((y-min_y+(size_x-size_y)/2)*width/size_x)]
        else:
            def shift_scale(xy):
                x, y = xy
                return [float((x-min_x+(-size_x+size_y)/2)*width/size_y), float((y-min_y)*width/size_y)]
        return shift_scale

    def animation_SVG(self, embeddings, fileName, edge_partition=None, first=None, totalTime=12, width=500, 
                           repetitions='indefinite', radius=15, disp=True,
                           rel_margin=0.1, thumbnail=True,colors=[]):
        if first==None:
            first = 2*floor(len(embeddings)/3)
        embeddings_shifted = embeddings[first:]+embeddings[:first]+[embeddings[first]]
        
        totalTime = str(totalTime)+'s'        
        shift_scale = self._shift_scale_fun(embeddings,  rel_margin, width)
        with open(fileName+'.svg','w') as f:
            f.write('<svg width="'+str(width)+'" height="'+str(width)
                    +'"  version="1.1" baseProfile="full"\n') #viewBox="0 0 500 350"
            f.write('xmlns="http://www.w3.org/2000/svg"\n')
            f.write('xmlns:xlink="http://www.w3.org/1999/xlink">\n')
            for v in self._graph.vertices():
                f.write('  <defs>\n')
                f.write('<marker id="vertex'+str(v)+'" viewBox="0 0 {1} {1}" refX="{0}" refY="{0}"\n'.format(radius, 2*radius))
                f.write(' markerWidth="{0}" markerHeight="{0}">\n'.format(floor(radius/3)))
                f.write('  <circle cx="{0}" cy="{0}" r="{0}" fill="grey" />\n'.format(radius))
                f.write('<text x="{0:0.0f}" y="{1:0.0f}" font-size="{1}" '.format(float(radius), float(1.5*radius))
                        +'text-anchor="middle" fill="white">'+str(v)+'</text>\n')
                f.write('</marker>\n')
                f.write('</defs>\n')

            colors = colors + ['LimeGreen','Orchid','Orange','Turquoise','SlateGray','LightGray']
            i = 0

            if edge_partition == None:
                edge_partition = [self._graph.edges(labels=False)]
            for edges_part in edge_partition:
                for u,v in edges_part:
                    embd = embeddings_shifted[0]
                    if i<6:
                        color = colors[i]
                    else:
                        color = 'black'
                    f.write('<path fill="transparent" stroke="'+color+'" stroke-width="5px" id="edge'
                            +str(u)+'-'+str(v)+'"'+
                        ' d="M {:0.0f} {:0.0f} L {:0.0f} {:0.0f}" '.format(*(shift_scale(embd[u]) +
                                                                shift_scale(embd[v])))
                        +'marker-start="url(#vertex'+str(u)+')"   marker-end="url(#vertex'+str(v)+')" />\n')
                i += 1

            for edges_part in edge_partition:
                for u,v in edges_part:
                    f.write('<animate ')
                    f.write('href="#edge'+str(u)+'-'+str(v)+'" ')
                    f.write('attributeName="d" ')
                    f.write('dur="'+totalTime+'" ')
                    f.write('repeatCount="'+str(repetitions)+'" ')
                    f.write('calcMode="linear" ')
                    path_str = ''
                    for embd in embeddings_shifted:
                        path_str = path_str+ 'M {:0.0f} {:0.0f} L {:0.0f} {:0.0f};'.format(*(shift_scale(embd[u]) +
                                                                shift_scale(embd[v])))
                    f.write('values="'+path_str+'"/>\n')

            f.write('</svg>\n')
        if disp:
            from IPython.display import SVG
            return SVG(fileName+'.svg')
#        if thumbnail:
#            self.createSVGandPNG(embeddings[first], fileName+'_thumbnail', edge_partition, width=width, colors=colors, radius=radius, rel_margin=rel_margin)















__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(GraphMotion)))
