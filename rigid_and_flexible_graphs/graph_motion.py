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
from sage.all import SageObject,  parent #, Subsets, rainbow, latex, flatten
from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
#from sage.rings.rational import Rational
from rigid_flexible_graph import RigidFlexibleGraph
import exceptions


class GraphMotion(SageObject):
    r"""

    """
    def __init__(self, graph, input_format, active_NACs, data, check):
        r"""


        TODO:

        Doc, examples
        """
        if not (isinstance(graph, RigidFlexibleGraph) or 'RigidFlexibleGraph' in str(type(graph))):
            raise exceptions.TypeError('The graph must be of the type RigidFlexibleGraph.')
        self._graph = graph
        self._parameter = None
        self._is_parametric = None
        self._par_type = 'symbolic'
        self._field = None
        self._same_lengths = None
        self._active_NACs = None
        if input_format == "grid":
            self._grid2motion(active_NACs[0], data,  check)
        elif input_format == "parametrization":
            self._parametrization2motion(active_NACs, data,  check)

    @staticmethod
    def GridConstruction(graph,  NAC_coloring,  zigzag=False,  check=True):
        return GraphMotion(graph, 'grid',  [NAC_coloring],  zigzag, check)


    @staticmethod
    def Parametrization(graph, parametrization, par_type,  active_NACs=None, check=True):
        return GraphMotion(graph, 'parametrization', active_NACs,  { 'parametrization' : parametrization,  'par_type' : par_type}, check)


    @staticmethod
    def Deltoid():
        pass

    def _grid2motion(self, NAC_coloring, zigzag, check):
        self._is_parametric = True
        self._par_type = 'symbolic'
        alpha = var('alpha')
        self._field = parent(alpha)
        self._parameter = alpha
        self._active_NACs = [NAC_coloring]
        grid_coor = NAC_coloring.grid_coordinates()
        self._same_lengths = []
        for i, edges in enumerate([NAC_coloring.blue_edges(), NAC_coloring.red_edges()]):
            partition = [[list(edges[0])]]
            for u, v in edges[1:]:
                appended = False
                for part in partition:
                    u2, v2 = part[0]
                    if Set([grid_coor[u][i], grid_coor[v][i]]) == Set([grid_coor[u2][i], grid_coor[v2][i]]):
                        part.append([u, v])
                        appended = True
                        break
                if not appended:
                    partition.append([[u, v]])
            self._same_lengths += partition

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

    def _parametrization2motion(self, active_NACs, data,  check):
        self._is_parametric = True
        self._parametrization = data['parametrization']
        element = (sum([self._parametrization[v][0]**Integer(2) for v in self._parametrization])
                    + sum([self._parametrization[v][1]**Integer(2) for v in self._parametrization]))
        self._field = parent(element)
        for v in self._parametrization:
            self._parametrization[v] = vector([self._field(x) for x in self._parametrization[v]])
        if data['par_type'] == 'symbolic':
            self._par_type = 'symbolic'
            if len(element.variables()) != 1:
                raise exceptions.ValueError('The parametrization has to have on parameter (' + str(len(element.variables())) + ' found).')
            self._parameter = element.variables()[0]
        if data['par_type'] == 'rational':
            self._par_type = 'rational'
            self._parameter = self._field.gen()

        if check:
            for u, v in self._graph.edges(labels=False):
                s = self._parametrization[u] - self._parametrization[v]
                l = s.inner_product(s)
                if self._par_type == 'rational' and not l in self._field.constant_field():
                    raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                if self._par_type == 'symbolic' and not l.simplify_full().is_constant():
                    raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')

        self._active_NACs = active_NACs

    def parametrization(self):
        r"""
        Return the parametrization.

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            return deepcopy(self._parametrization)
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def realization(self, value,  numeric=False):
        r"""
        Return the realization for given value of the parameter.

        TODO:

        Doc, examples
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
            elif self._par_type == 'rational':
                h = self._field.hom(value)
                for v in self._parametrization:
                    if numeric:
                        res[v] = vector([RR(h(xi)) for xi in self._parametrization[v]])
                    else:
                        res[v] = vector([h(xi) for xi in self._parametrization[v]])
                return res
            else:
                raise exceptions.NotImplementedError('')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def sample_parametrization(self, N,  sampling):
        r"""
        Return a sampling of the motion.

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            interval = []
            if type(sampling) == list and len(sampling) == 2:
                sampling_type,  interval = sampling
            else:
                sampling_type = sampling
            if len(interval) != 2:
                a = -pi
                b = pi
            else:
                a, b = interval
            if sampling_type == 'uniform':
                return [self.realization(RR(a + (i/Integer(N)) * (b-a)),  numeric=True) for i in range(0, N+1)]
            elif sampling_type == 'tan':
                return [self.realization(tan(RR(a + (i/Integer(N)) * (b-a))/2.0),  numeric=True) for i in range(0, N+1)]
            else:
                raise exceptions.NotImplementedError('Sampling ' + str(sampling) + ' is not supported.')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')

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

    def animation_SVG(self, fileName, sampling='uniform', edge_partition=True, first=None, totalTime=12, width=500,
                           repetitions='indefinite', radius=15, return_IPythonSVG=True, fps=25,
                           flipY=True,
                           rel_margin=0.1,colors=[]):
        r"""
        Save an SVG animation.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: M = GraphMotion.GridConstruction(G, delta.conjugated(), zigzag=[[[0,0], [0,1]], [[0,0], [3/4,1/2], [2,0]]])
            sage: M.animation_SVG('animation')
            <IPython.core.display.SVG object>

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            realizations = self.sample_parametrization(totalTime*fps,  sampling)
            if first==None:
                first = 2*floor(len(realizations)/3)

            if flipY:
                for embd in realizations:
                    for v in embd:
                        embd[v][1] = -embd[v][1]

            totalTime = str(totalTime)+'s'
            shift_scale = self._shift_scale_fun(realizations,  rel_margin, width)
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

                default_colors = ['LimeGreen','Orchid','Orange','Turquoise','SlateGray','LightGray']
                colors = colors + default_colors
                i = 0

                if edge_partition:
                    if type(edge_partition) == list:
                        pass
                    elif self._same_lengths:
                        edge_partition = self._same_lengths
                    else:
                        edge_partition = [self._graph.edges(labels=False)]
                        if len(colors) == len(default_colors):
                            colors = ['LightGray']

                for edges_part in edge_partition:
                    for u,v in edges_part:
                        embd = realizations[first]
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
                        for embd in realizations[first:]+realizations[:first]: #+[realizations[first]]
                            path_str = path_str+ 'M {:0.0f} {:0.0f} L {:0.0f} {:0.0f};'.format(*(shift_scale(embd[u]) +
                                                                    shift_scale(embd[v])))
                        f.write('values="'+path_str+'"/>\n')

                f.write('</svg>\n')
            if return_IPythonSVG:
                from IPython.display import SVG
                return SVG(fileName+'.svg')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')















__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(GraphMotion)))
