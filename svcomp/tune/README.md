# SMACKTune
An automatic parameter tuning framework for SMACK

## Installation

To install, simply run `./setup.sh`.  This installs ruby, downloads the
paramils tool, and copies this tool, along with the paramils configuration
for SMACK to `../../../SMACKTune`, by default.

## SMACKTune Organization

ParamILS calls each tuning configuration a "scenario".  SMACKTune adopts this
terminology.

SMACKTune gets installed to `../../../SMACKTune`, relative to this folder.  The
ParamILS package gets unzipped here, as do the `lib` and `scenarios` folders.
Finally, the `run.py` script gets copied to this main `SMACKTune` folder, as 
well.

The `lib` folder contains scripts and other resources common to all scenarios.

The `scenarios` folder contains preconfigured scenarios that can be used "out
of the box", or used as templates for creating new tuning scenarios.

When `run.py` is executed, its results can be found in the `./results` folder.
See the "Tuning Parameters" section for details on `run.py` usage.

## Scenario Requirements

Scenario folders are folders containing configurations for tuning with
ParamILS.  All scenario folders must be located in the `./scenarios` folder.
The name of the scenario folder will constitute the name of the scenario.
For example, a scenario called XYZ should have a corresponding scenario folder,
`./scenarios/XYZ/`.  Results for tuning this scenario will be found in 
`./results/XYZ/`.

Each scenario folder must contain some required files to 

## Establishing Performance Baselines

Our configuration of paramils optimizes the geometric mean of speedups for 
defining the "best" parameter configuration.  To accomodate this, it is
necessary to collect run times of benchmarks on which tuning will be done,
to establish a baseline run time for each benchmark.  (Consider two benchmarks.
One takes 30 seconds to verify, the other 90 seconds, using the default SMACK
paramaters.  If we used strict runtime instead of speedup, it wouldn't make
sense to compare runtimes of the two benchmarks, since one is inherently more
complex -- trying different parameters for the 90 second benchmark is still
likely to take longer than the 30 second benchmark, and so a strict runtime
comparison will look like an inferior parameter selection as compared to the 30
second benchmark, even though the 90 second benchmark may finish in 70 seconds
with the new parameter selection - obviously an improvement).

To establish this baseline for each benchmark in a configuration set, it is
necessary to run SMACK with its default parameters on each benchmark.  To do
this, simply run `<command here>`.  This will also generate a paramils
"instance file" for the input benchmark set.  This file contains each benchmark
file name, along with its baseline execution time.  This instance file
generation should be performed any time SMACKTune is deployed to a new machine,
to make sure that the baselines are calibrated for that specific machine's
hardware.

## Tuning Parameters

Once an instance file has been generated for a scenario, tuning can begin.  To 
begin the tuning process, simply run `run.py <scenarioFolder> <threadCount>`.
This will launch paramILS `<threadCount>` times.  Each concurrent run is an
independent tuning of SMACK -- because paramILS does a local search, it is 
possible that each concurrent run will return different optimum input
parameters.  Ideally, convergence on a single set of input parameters will be
seen across the set of multiple concurrent runs.

All results for a call to `run.py` will be placed in a folder called
`results-<scenarioFolder>-<timestamp>`, where `<scenarioFolder>` is the same
folder identified by the input parameter to `run.py`.

## Selecting Best Parameters

Something about finding convergence of multiple runs, and running these on
an additional set of benchmarks.