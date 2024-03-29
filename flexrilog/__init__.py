#Copyright (C) 2019 Jan Legersky
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


import sage.all
from .graph_motion import GraphMotion, ParametricGraphMotion
from .flexible_rigid_graph import FlexRiGraph, FlexRiGraphWithCartesianNACs
from .framework import Framework
from .braced_Pframework import Pframework, BracedPframework
from .symmetric_flexible_rigid_graph import SymmetricFlexRiGraph, CnSymmetricFlexRiGraph, CnSymmetricFlexRiGraphCartesianNACs, CsSymmetricFlexRiGraph
from .graph_generator import GraphGenerator, GraphDrawer
from .NAC_coloring import NACcoloring
from .symmetric_NAC_coloring import CnSymmetricNACcoloring, PseudoRScoloring
from .motion_classification import MotionClassifier


colB = '#4169e1'
colR = '#ee2c2c'
colGray = 'LightGray'
colG = '#FFD700'