##===- projects/smack/Makefile ----------------------------*- Makefile -*-===##
#
# This is a Makefile for SMACK.
#
##===----------------------------------------------------------------------===##

#
# Indicates our relative path to the top of the project's root directory.
#
LEVEL = .
DIRS = lib tools
EXTRA_DIST = include

#
# Include the Master Makefile that knows how to build all.
#
include $(LEVEL)/Makefile.common

#
# Standardized source code formatting.
# -- probably should be run systematically with build.
#
format:
	astyle --options=astyle.conf $$(find lib -name "*.cpp")
	astyle --options=astyle.conf $$(find include -name "*.h")
	
distclean:: clean
	${RM} -f Makefile.common Makefile.config