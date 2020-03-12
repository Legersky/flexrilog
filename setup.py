## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests


# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib --show-skipped -i -p 4 flexrilog")
        if errno != 0:
            sys.exit(1)
            
class SageTestLong(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --long --force-lib -i -p 4  flexrilog")
        if errno != 0:
            sys.exit(1)
             
class SageTestOptional(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --long --force-lib --optional=build,dochtml,memlimit,mpir,sage,lnumber,phcpy -i -p 4 flexrilog")
        if errno != 0:
            sys.exit(1)

setup(
    name = "flexrilog",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='FlexRiLoG - A package for investigating Flexible and Rigid Labelings of Graphs',
    long_description = readfile("README.rst"), # get the long description from the README
    long_description_content_type = 'text/x-rst',
    url='https://github.com/legersky/flexrilog',
    author='Jan Legerský, Georg Grasegger',
    author_email='jan.legersky@risc.jku.at', # choose a main contact email
    license='GPLv3+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 4 - Beta',
      'Intended Audience :: Science/Research',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)',
      'Programming Language :: Python :: 3.7',
    ],
    keywords = "rigidity flexibility",
    packages = ['flexrilog'],
    cmdclass = {'test': SageTest,  # adding a special setup command for tests
                'testLong': SageTestLong, 
                'testAll': SageTestOptional},
    setup_requires   = ['sage-package'],
    install_requires = ['sage-package', 'sphinx'],
)
