# Put them all here when creating executable, so they are included.
require "stats_ils.rb"
#require "spear_reader.rb"
#require "sat4j_reader.rb"
#require "ubcsat_reader.rb"
#require "cplex_reader.rb"

class Object
      def deep_clone
        Marshal::load(Marshal.dump(self))
      end
    end
    

###########################################################################
# Simple pseudo-random number generator using system time. From: http://gnuvince.net/?p=134
# I'm using it to create temporary file names etc. Don't use rand for repeatability of runs when reading saved results from the DB instead.
###########################################################################
def random_number_without_rand
  t = Time.now.to_f / (Time.now.to_f % Time.now.to_i)
  random_seed = t * 1103515245 + 12345;
  a=(random_seed / 65536) % 32768;
  return a/32768
end


$max_objective = 100000000000000
    
###########################################################################
#Build algorun_cmd
###########################################################################
def buildAlgorunCmd(algo, stripped_state_int, instance_relname, desired_solqual, cutoff_time, cutoff_length, db=true)
	algo_config_id = 0
	raise "when getting to buildAlgorunCmd, stripped_state_int has to be an Integer. It is #{stripped_state_int}" unless stripped_state_int.is_a?(Integer)
	params = $stripped_int_to_stripped_state[stripped_state_int]
	if algo == "saps"
		#=== Define default parameters that are used unless specifed differently.
#		defaults = {"alpha"=>1.3, "rho"=>0.8, "ps"=>0.05, "wp"=>0.01}
		
		executable = "./ubcsat -alg saps"
		cutoff_length = "max" if cutoff_length == "-1"  #Want to save an integer in the DB
		cmd_suffix = "-inst #{instance_relname} -cutoff #{cutoff_length} -timeout #{cutoff_time} -r out stdout run,found,seed,best,beststep,steps,time"
		cutoff_length = 2147483647 if cutoff_length == "max"  #Want to save an integer in the DB
		if params["param_string"] == "default-params"
			param_string = ""
		else
			param_string = params.keys.sort.map{|key| "-#{key} #{params[key]}"}.join(" ")
		end
	elsif algo == "novelty+"
		executable = "./ubcsat -alg novelty+"
		cutoff_length = "max" if cutoff_length == "-1"  #Want to save an integer in the DB
		cmd_suffix = "-inst #{instance_relname} -cutoff #{cutoff_length} -timeout #{cutoff_time} -r out stdout run,found,seed,best,beststep,steps,time"
		cutoff_length = 2147483647 if cutoff_length == "max"  #Want to save an integer in the DB
		param_string = params.keys.sort.map{|key| "-#{key} #{params[key]}"}.join(" ")
		
	elsif algo == "cplex"
		#=== CPLEX is a special case: I'm calling a ruby script that in turn calls the command line interpreter.
		executable = "ruby ../scripts/cplex_wrapper.rb #{instance_relname} #{cutoff_time}"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| value = params[key]; value = "'#{params[key]}'" unless params[key].include?("'"); "-#{key} #{value}"}.join(" ")
		end
		cmd_suffix = ""
	
	elsif algo == "branin_function"
		#=== Define default parameters that are used unless specifed differently.
#		defaults = {"x"=>2.5, "y"=>7.5}
		executable = "ruby exponential_function_with_branin_fucntion_as_median.rb"
		cmd_suffix = "#{cutoff_time}"
		param_string = params.keys.sort.map{|key| "-#{key} #{params[key]}"}.join(" ")
		
	elsif algo == "sls4mpe" or algo == "gls4mpe"
		#=== Define default parameters that are used unless specifed differently.
		defaults = {} # I think this is redundant !
		executable = "./sls4mpe"
#		cmd_suffix = "-i #{instance_relname} --optimalLogMPE #{desired_solqual} -t #{cutoff_time}"
		cmd_suffix = "-i #{instance_relname} -t #{cutoff_time}" # Do NOT stop if best known qual achieved, may improve !
		if params["param_string"] == "default-params"
			param_string = ""
		else
			param_string = params.keys.sort.map{|key| "-#{key} #{params[key]}"}.join(" ")
		end
	elsif algo == "sat4j"
		#=== Prepare SAT4J command line parameters.
		executable = "/usr/bin/java -Xms300M -Xmx300M -jar sat4j.jar"
		cmd_suffix =  "-t #{cutoff_time.ceil.to_i} #{instance_relname}"

		if params["param_string"] == "default-params"
#		if params["default-params"] == true
			param_string = ""
		else
			params = strip_state(params)

			param_string = "-S DSF=#{params["DSF"]},LEARNING=#{params["LEARNING"]}"
			param_string += "/activityPercent:#{params["activityPercent"]}" if params.key?("activityPercent")
			param_string += "/maxLength:#{params["maxLength"]}" if params.key?("maxLength")
			param_string += "/limit:#{params["limit"]}" if params.key?("limit")
			param_string += ",ORDER=#{params["ORDER"]}"
			param_string += "/period:#{params["period"]}" if params.key?("period")
			param_string += ",SIMP=#{params["SIMP"]}"
			param_string += ",PARAMS=org.sat4j.minisat.core.SearchParams/varDecay:#{params["varDecay"]}/claDecay:#{params["claDecay"]}/conflictBoundIncFactor:#{params["conflictBoundIncFactor"]}/initConflictBound:#{params["initConflictBound"]}"
		end
		
	elsif algo == "spear0.9" or algo == "spear"
		executable = "./Spear-32"
		cmd_suffix = "--nosplash --stats --version --tmout #{cutoff_time.to_i} --dimacs #{instance_relname}"
		if params["param_string"] == "default-params"
#		if params["default-params"] == true
			param_string = ""
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end
		
	elsif algo == "spear1.2.1" or algo == "spear1.2.1.1"
		executable = "./Spear-32_1.2.1"
		cmd_suffix = "--nosplash --stats --version --tmout #{cutoff_time.ceil.to_i} --dimacs #{instance_relname}"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end

	elsif algo == "spear2.2"
		executable = "./Spear_v2.2_xeon"
		cmd_suffix = "--nosplash --stats --version --tmout #{cutoff_time.ceil.to_i} --dimacs #{instance_relname}"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end

	elsif algo == "spear2.3"
		executable = "./Spear_v2.3"
		cmd_suffix = "--nosplash --stats --version --tmout #{cutoff_time.ceil.to_i} --dimacs #{instance_relname}"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end

	elsif algo == "smt"
		executable = "./Spear_i586_32_Linux-07-06-19"
		cmd_suffix = "--nosplash --stats --tmout #{cutoff_time.ceil.to_i} --sf #{instance_relname}"
#		cmd = "./Spear --nosplash --time #{paramstring} --sf #{input_file} --tmout #{timeout} --seed #{seed}"
		
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end

	elsif algo == "spear1.2"
		executable = "./Spear-32_1.2"
		cmd_suffix = "--nosplash --stats --version --tmout #{cutoff_time.to_i} --dimacs #{instance_relname}"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| "--#{key} #{params[key]}"}.join(" ")
		end

	elsif algo == "param_ils_metatune"
		#=== CPLEX is a special case: I'm calling a ruby script that sends a bunch of tuning jobs off to the cluster, waits for them to finish, and then returns their performance.
		#=== instance_relname here stands for the seed I'm passing to the base tuner (normally, I'd use the seed for that, but that doesn't work since it's unknown at this point and the scripts are set up for it to be passed here).
		#=== A run of all tuning scenarios together is treated as a single run. 
		#=== desired_solqual encodes training (0) or test performance (1)
##		executable = "ruby ../param_ils_metatune/param_ils_caller_for_metatuning.rb #{instance_relname} #{desired_solqual} #{cutoff_time} not_used_cutoff_length not_used_seed"
#		executable = "ruby ../param_ils_metatune/param_ils_caller_for_metatuning.rb #{instance_relname} not_used_qual #{cutoff_time} not_used_cutoff_length placeholder_for_seed"
		executable = "ruby ../param_ils_metatune/new_param_ils_caller_for_metatuning.rb #{instance_relname} not_used_qual #{cutoff_time} not_used_cutoff_length placeholder_for_seed"
		if params["param_string"]
			param_string = params["param_string"]
			param_string = "" if params["param_string"] == "default-params"
		else
			param_string = params.keys.sort.map{|key| value = params[key]; value = "'#{params[key]}'" unless params[key].include?("'"); "-#{key} #{value}"}.join(" ")
		end
		cmd_suffix = ""
		
	elsif algo == "satenstein"
		executable = "./ubcsat -alg satenstein"
		cutoff_length = "max" if cutoff_length == "-1"  #Want to save an integer in the DB
		cmd_suffix = "-inst #{instance_relname} -cutoff #{cutoff_length} -timeout #{cutoff_time} -r out stdout run,found,seed,best,beststep,steps,time"
		cutoff_length = 2147483647 if cutoff_length == "max"  #Want to save an integer in the DB
		if params["param_string"] == "default-params"
			param_string = ""
		else
			param_string = params.keys.sort.map{|key| "-#{key} #{params[key]}"}.join(" ")
		end

	else	
		p algo
		raise "Need to specify executable and default parameters for algo #{algo} in function buildAlgorunCmd of algo_specifics.rb"
	end

#	if params.key?("param_string")
#		param_string = params["param_string"]
#	end


=begin
#=== Generic treatment for each algo: check parameters and fill unspecified parameters with their default settings.
	for key in params.keys 
		raise "Unknown parameter #{key} for #{algo}" unless defaults.key?(key)
	end
	for key in defaults.keys
		params[key] = defaults[key] unless params.key?(key)
	end
=end

	algorun_cmd = "#{executable} #{param_string} #{cmd_suffix}"
#	puts algorun_cmd 

	if db
		if algo == "saps"
			algo_config_id = get_saps_config_id(params)
		elsif algo == "novelty+"
			algo_config_id = get_novelty_plus_config_id([params["novnoise"], params["wp"]])
		elsif algo == "sat4j"
			algo_config_id = get_sat4j_config_id(params)
		elsif algo == "spear0.9"
			algo_config_id = get_spear_1_0_config_id(params)
		elsif algo == "spear1.2.1" or algo == "spear1.2" or algo == "spear1.2.1.1"
			algo_config_id = get_algo_config_id(params, "SPEAR_CONFIGURATION_1_2")
		elsif algo == "spear2.2" 
			algo_config_id = get_algo_config_id(params, "SPEAR_CONFIGURATION_2_2")
		elsif algo == "spear2.3" 
			algo_config_id = get_algo_config_id(params, "SPEAR_CONFIGURATION_2_3")
		elsif algo == "spear-orig"
			algo_config_id = get_orig_spear_config_id(params)
		elsif algo == "gls4mpe"
			algo_config_id = get_gls4mpe_config_id(params)
		elsif algo == "cplex"
			algo_config_id = get_algo_config_id(params, "CPLEX_CONFIGURATION_10_1_1")
#			get_cplex_10_1_1_config_id(params)
		elsif algo == "smt"
			algo_config_id = get_algo_config_id(params, "SPEAR_CONFIGURATION_1_8")
		elsif algo == "param_ils_metatune"
			algo_config_id = get_algo_config_id(params, "PARAM_ILS_METATUNE_1_0")
			#raise "ParamILS Metatuner should NOT use the DB."
		elsif algo == "satenstein"
			algo_config_id = get_algo_config_id(params, "SATENSTEIN_CONFIGURATION_FH")
		else
			#algo_config_id = get_general_algorithm_config_id(algo, param_string)
			raise "Need to implement method to get algo_config_id for algo #{algo} in function buildAlgorunCmd of global_helper.rb"
		end
	end

	#=== Build command to run. (concat pairs of "-param param_value")
	return [algorun_cmd, cutoff_length, algo_config_id]
end


###########################################################################
# Run algorithm and save its result to DB.
###########################################################################
def runalgo(algorun_config_id, seed)
	require "dbi_ils_accessor.rb"
	host = nil
	File.popen("echo $HOSTNAME"){|file|
		while line = file.gets
			host = line.chomp
			puts line
		end
#		host = file.gets.chomp
	}
	algo, algorun_cmd = get_algo_and_runcmd_for_algorunconfig(algorun_config_id)
#	File.popen("pwd"){|file| puts "Dir = #{file.gets.chomp}"}
	
	t = Time.now
	datetime = t.strftime("%Y-%m-%d %H:%M:%S") # YYYY-MM-DD HH:MM:SS
	algo_output_file = "#{tmpdir}/tmp-#{datetime}-#{random_number_without_rand}".gsub(/ /,"")
    
	numTries = 5

	if algo == "saps"
		#4294967295
#		puts "SAPS seed = #{seed}" 
		raise "seed too big: #{seed}" if seed >= 2147483647

		#=== SAPS -> Call special code to parse non-trivial UBCSAT output. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} -seed #{seed} > #{algo_output_file}" #-runs 1
		run_cmd = "./" + run_cmd unless run_cmd =~/^\.\//
		require "ubcsat_reader.rb"
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readUbcsatAndWriteToDB(algo_output_file, algorun_config_id, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end
		
	elsif algo == "satenstein"
#		puts "SAPS seed = #{seed}" 
		raise "seed too big: #{seed}" if seed >= 2147483647

		#=== SATENSTEIN -> Call special code to parse non-trivial UBCSAT output. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} -seed #{seed} > #{algo_output_file}" #-runs 1
		run_cmd = "./" + run_cmd unless run_cmd =~/^\.\//
		require "ubcsat_reader.rb"
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readUbcsatAndWriteToDB(algo_output_file, algorun_config_id, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end


	elsif algo == "novelty+"
		raise "seed too big: #{seed}" if seed >= 2147483647

		#=== Novelty+ -> Call special code to parse non-trivial UBCSAT output. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} -seed #{seed} > #{algo_output_file}" #-runs 1
		run_cmd = "./" + run_cmd unless run_cmd =~/^\.\//
		require "ubcsat_reader.rb"
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readUbcsatAndWriteToDB(algo_output_file, algorun_config_id, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end
		
	elsif algo == "cplex"
		raise "CPLEX is deterministic. The seed value has to be zero for deterministic algorithms, probably there is a bug somewhere." unless seed==-1

		#=== CPLEX -> Parse fairly simple output from our wrapper. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} #{algo_output_file}"
		puts "  Calling #{run_cmd}"
		require "cplex_reader.rb"
		#=== Keep on trying to run until we get a license.
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readCPLEXAndWriteToDB(algo_output_file, algorun_config_id, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				sleep(10)
				File.delete(algo_output_file) if File.file?(algo_output_file)
				retry
			else 
				raise
			end
		end
		
	elsif algo == "param_ils_metatune"
		run_cmd = "#{algorun_cmd.sub(/placeholder_for_seed/, "#{seed}")} > #{algo_output_file}"
		puts "Calling: #{run_cmd}"
		system run_cmd
		
		content=""
		File.open(algo_output_file, "r"){|algo_output|
			content = algo_output.gets(nil)
		}
    		add_algo_output_cmd = "insert into FH_OUTPUT (OUTPUT_TEXT) values (\"#{content.gsub(/\"/,"")}\")"
		algo_output_id = execute_cmd_with_quotes_one_autoincrement(add_algo_output_cmd, true)
		
		File.open(algo_output_file){|file|
			while line = file.gets
				if line =~ /Final Result for ParamILS: /
					line = line.sub(/Final Result for ParamILS: /,"")
					puts "Result: #{line.strip}"
					solved, runtime, runlength, best_sol, tmpseed = line.split(",").map!{|x|x.strip}
					p [solved, runtime, runlength, best_sol, seed]
					writeResultToDB(algorun_config_id, seed, runtime, runlength, best_sol, 0, 'SAT', algo_output_id, host)
					break
				end
			end
		}
		
	elsif algo == "param_ils_metatune"
		run_cmd = "#{algorun_cmd.sub(/placeholder_for_seed/, "#{seed}")} > #{algo_output_file}"
		puts "Calling: #{run_cmd}"
		system run_cmd
		
		content=""
		File.open(algo_output_file, "r"){|algo_output|
			content = algo_output.gets(nil)
		}
    		add_algo_output_cmd = "insert into FH_OUTPUT (OUTPUT_TEXT) values (\"#{content.gsub(/\"/,"")}\")"
		algo_output_id = execute_cmd_with_quotes_one_autoincrement(add_algo_output_cmd, true)
		
		File.open(algo_output_file){|file|
			while line = file.gets
				if line =~ /Final Result for ParamILS: /
					line = line.sub(/Final Result for ParamILS: /,"")
					puts "Result: #{line.strip}"
					solved, runtime, runlength, best_sol, tmpseed = line.split(",").map!{|x|x.strip}
					p [solved, runtime, runlength, best_sol, seed]
					writeResultToDB(algorun_config_id, seed, runtime, runlength, best_sol, 0, 'SAT', algo_output_id, host)
					break
				end
			end
		}
		
	elsif algo == "sat4j"
		raise "SAT4J is deterministic. The seed value has to be zero for deterministic algorithms, probably there is a bug somewhere." unless seed==-1

		#=== SAT4J -> Parse fairly simple output. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} > #{algo_output_file}"
		require "sat4j_reader.rb"
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readSAT4JAndWriteToDB(algo_output_file, algorun_config_id, host)
			exit_code = $?
			p exit_code.to_s
			if exit_code.to_s =~ /33280/ # /exited\(1\)/
				raise "SAT4J was terminated by user (exit code #{exit_code}"
			end
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end

elsif algo == "sls4mpe" or algo == "gls4mpe"
		seed = (seed-1).divmod(2147483647)[1]+1  # can't use seed=0 for this implementation
		puts "SLS4MPE seed = #{seed}" 
				
		#=== SLS4MPE -> Call special code to parse non-trivial output. We also want to keep track of the whole output file.
		run_cmd = "#{algorun_cmd} --seed #{seed} -x 1 > #{algo_output_file}"
		run_cmd = "./" + run_cmd unless run_cmd =~/^\.\//
		require "sls4mpe_reader.rb"
		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readSLS4MPEAndWriteToDB(algo_output_file, algorun_config_id, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end

	elsif algo == "spear0.9"
		run_cmd = "#{algorun_cmd} > #{algo_output_file}"
		puts "  Calling #{run_cmd}"
		system run_cmd

		require "spear_reader.rb"
		readSpearAndWriteToDB(algo_output_file, algorun_config_id, seed, host)
		File.delete(algo_output_file)
	elsif algo == "spear1.2.1" or algo == "spear1.2" or algo == "spear1.2.1.1"
		run_cmd = "#{algorun_cmd} --seed #{seed} > #{algo_output_file}"
		require "spear_reader.rb"

		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readSpearAndWriteToDB(algo_output_file, algorun_config_id, seed, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end

	elsif algo == "spear2.2" or algo == "spear2.3"
		run_cmd = "#{algorun_cmd} --seed #{seed} > #{algo_output_file}"
		require "spear_reader.rb"

		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readSpearAndWriteToDB(algo_output_file, algorun_config_id, seed, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end

	elsif algo == "smt" 
		run_cmd = "#{algorun_cmd} --seed #{seed} > #{algo_output_file}"
		require "spear_reader.rb"

		i = 0
		begin
			puts "  Trial #{i} for calling: #{run_cmd}"
			system run_cmd
			readSpearAndWriteToDB(algo_output_file, algorun_config_id, seed, host)
			File.delete(algo_output_file) if File.file?(algo_output_file)
		rescue #=== Catch error due to files disappearing
			if $!.to_s =~ /No such file or directory/ or $!.to_s =~ /Input\output error/ or $!.to_s =~ /Stale NFS file handle/
				i += 1
				retry if i < numTries
			else 
				raise
			end
		end
	elsif algo == "branin_function" 
		#=== Branin function script -> simple output, just parse here. Possibly pass seed on to noise from exponential distribution.
		run_cmd = "#{algorun_cmd} #{numRuns}"
		puts "Calling: #{run_cmd}"
		mysql_cmds = []
		File.popen(run_cmd){|file|
			while line = file.gets
				puts line
				if line =~/Observed value (#{float_regexp})./
					result = $1
					if line =~ /Solved./
						solved = "SAT"
					else
						solved = "TIMEOUT"
					end
		        		mysql_cmds << "insert into ALGORUN (ALGORUN_CONFIG_ID,MEASURED_RUNTIME,SOLVED, DATE) VALUES (#{algorun_config_id}, #{result}, '#{solved}', now());"
				end
			end
		}
	        raise "No branin_function run generated by command #{run_cmd}}" unless mysql_cmds.length > 0
		execute_cmds(mysql_cmds)
	else    
		raise "Algo #{algo} not implemented yet."
	end
end



###########################################################################
# Outputs the objective function values for each of the instances -- mainly for CALIBRA.
# An instanceHash is a Hash {instance_name=>{"desired_qual"=>optqual, "result"=>[res_1, res_2, ..., res_numLsRuns]}} where res_i = [time, steps, solqual_found]
###########################################################################
def outputObjectives(instances_sorted, objectives)
	raise "not a result for each instance: #{instances_sorted}, #{objectives}" unless instances_sorted.length == objectives.length

	for i in 0...objectives.length
		puts "#{instances_sorted[i]}: #{objectives[i][0]}\t\t[based on #{objectives[i][1]} runs]"
	end
end


def outputCalibraObjectivesFairEval(algo, within_obj, obj_function, instances_sorted, objectives)
	raise "not a result for each instance: #{instances_sorted}, #{objectives}" unless instances_sorted.length == objectives.length

	for i in 0...objectives.length
		if within_obj == "runtime" or within_obj == "median_runtime"
			obj = objectives[i][0]+1
			obj = 1000 if obj > 1000
		elsif within_obj  == "runlength" or within_obj  == "median_runlength"
			if 1+objectives[i][0] > 1000000*1000
				obj = 1000
			else
				obj = 1 + objectives[i][0].to_f / 1000000
			end
		elsif algo == "branin_function"
			obj = 1 + objectives[i][0] 
		elsif algo == "sls4mpe"
			obj = 1 + objectives[i][0] 
		elsif algo == "gls4mpe"
			obj = 1 + objectives[i][0] 
		else
			raise "Need to implement calibra output function for algorithm #{algo}."
		end
		
		puts "Calibra objective: #{obj}\n  [based on #{objectives[i][1]} runs for #{instances_sorted[i]}]"
	end
	puts "Total runtime: #{$total_cputime}"
end


###########################################################################
# Extract the appropriate value for the algorithm from the result [runtime, runlength, qual_found, des_qual]
###########################################################################
def singleRunObjective(algo, run_obj, result, qual, rest, cutoff_time=100, cutoff_length=2147483647)
	raise "singleRunObjective: result = #{result}" unless result 
	eps = 0.0001
	solved, runtime, runlength, found_qual, seed = result #.map{|x|x.to_f}


	if run_obj == "SATRace08"
		t = 900
		score = 0
#		p result
#		p runtime
		unless solved == "TIMEOUT" or runtime.to_f > t
			score = score + 1
			x = 1.3 # that's what this constant worked out to be in the SAT Race 2006
			numsuccesful = 1
#			p qual
#			p rest
			if qual
				other_runtimes = [qual]
			else
				other_runtimes = []
			end				
			other_runtimes += rest
#			p other_runtimes 
			for other_runtime in other_runtimes
				if other_runtime.to_f < 10000
					numsuccesful = numsuccesful + 1
				end
			end
			p_max = x/numsuccesful;
			score = score + p_max * (1-runtime.to_f/t)
		end
#		p result
#		p runtime
#		p other_runtimes
#		p score
		return -score
	end

	if solved == "TIMEOUT" 
		#=== Break ties by solution quality (negative quality counted as 0). 
		runtime = cutoff_time + 1e-5 + [0.001, [0, found_qual.to_f/1e5].max].min  # replaced [0.001, found_qual.abs.to_f/1e5].min. The 1e-5 is there to avoid numerical problem, so this is > cutoff_time for sure. The min(0.001, ...) is such that it really only acts as a tie breaker, and the max(0, ...) is such that negative qualities don't screw us up.
		runlength = runlength + [0.001, found_qual.abs.to_f/1e5].min # just for tie-breaking. I am NOT using cutoff_length anymore.
		score = 0
	elsif solved == "WRONG ANSWER" || solved == "WRONG" || solved == "CRASHED"
		runtime = cutoff_time  + [0.001, found_qual.abs.to_f/1e5].min
		runlength = runlength  + [0.001, found_qual.abs.to_f/1e5].min
		score = 0
	elsif solved == "ABORT"
		puts "Got an ABORT message from the wrapper command. ABORTING PARAMILS."
		exit -1
	else
		runtime = runlength.to_f/100000 if runtime.to_f < 0.0001 # to break ties when all runtimes are 0
		runtime = runtime.to_f
		runlength = runlength.to_i
		score = -1.0/(1.0+runtime.to_f)
		found_qual = found_qual.to_f
	end

	return found_qual if run_obj == "qual"
	return runlength if run_obj == "runlength" or run_obj == "median_runlength"
	return runtime if run_obj == "runtime" or run_obj == "median_runtime"
	return score if run_obj == "score"
	if run_obj == "approx"
		approx_qual = qual.to_f/found_qual # <= 1, want to max
		return 1 - approx_qual
	end
	if run_obj == "prob"
#		p reference
#		p found_qual
#		p result
		diff = qual.to_f-found_qual  # average only over runs on this instance.
		return 10 ** diff
	end
	if run_obj == "speedup"
		ref = rest[0].to_f
		ref = 0.01 if ref < 0.00001
		ref = 10000 if ref > 999.99999 #timeout
		runtime=0.01 if runtime < 0.00001
		runtime = 10000 if runtime == $max_objective #timeout
		speedup = runtime/ref
#		puts "#{runtime} / #{ref} = #{speedup}"
		return speedup
	end
	raise "Need to define run_obj #{run_obj} in singleRunObjective in algo_specifics."
end


def getObjectivesForComputedInstances(algo, within_obj, instances, instances_sorted, state_as_string)
	#=== Results are stored directly in the instances array. Just extract them.
	runsWithResults = []
	resultsCanExist = true
	for entry in instances
		if entry["resultForState"].key?(state_as_string)
			raise "@instances array has no result for early instance but result for latter one: state #{state_as_string}, @instances #{@instances}" unless resultsCanExist
			runsWithResults << entry
		else
			resultsCanExist = false  #=== Just as a safety check.
		end
	end
	return getAllObjectives(algo, within_obj, runsWithResults, instances_sorted, state_as_string)
end

def getGlobalObjective(algo, within_obj, obj_function, instances, state_as_string, cutoff_time=100, cutoff_length=2147483647)
#	require "stats_ils.rb"
	results = []
	for entry in instances
		if entry["resultForState"].key?(state_as_string)
			if entry["resultForState"][state_as_string].key?(cutoff_time)
				result = entry["resultForState"][state_as_string][cutoff_time]
			else
				cutoff_times = entry["resultForState"][state_as_string].keys
				result = entry["resultForState"][state_as_string][cutoff_times.max]
			end
			#results << singleInstanceObjective(algo, within_obj, [result], entry["qual"], entry["reference"])
			results << singleRunObjective(algo, within_obj, result, entry["desired_qual"], entry["rest"], cutoff_time, cutoff_length)
		end
	end
#	return [results.avg, results.length]
	return [combinationOfObjectiveFunctions(algo, obj_function, results, within_obj, cutoff_time, cutoff_length), results.length]
end

###########################################################################
# Extract the appropriate value for the algorithm from the result [runtime, runlength, qual_found, des_qual]
###########################################################################
def getAllObjectives(algo, within_obj, instances, instances_sorted, stripped_state_int, cutoff_time=100, cutoff_length=2147483647)	
	instanceHash = makeStandardInstanceHash(instances, stripped_state_int)
	
	objectives = []
	for inst in instances_sorted
		if instanceHash.key?(inst)
			result = instanceHash[inst]["result"]
			p result
			qual = instanceHash[inst]["desired_qual"]
			rest = instanceHash[inst]["rest"]
			results = []
			for res in result
				results << singleRunObjective(algo, within_obj, res, qual, rest, cutoff_time, cutoff_length)
			end
#			require "stats_ils.rb"
			objectives << [results.median, results.length]
#			objectives << [singleInstanceObjective(algo, within_obj, result, qual, reference), result.length]
		else
			objectives << [nil, 0]
		end
	end
	return objectives
end

###########################################################################
# Summarize the results as one float.
###########################################################################
def combinationOfObjectiveFunctions(algo, obj_function, instanceObjectives, within_obj = "runtime", cutoff_time=100, cutoff_length=2147483647)
	return $max_objective * 10000 if instanceObjectives.empty?

	maxOK = cutoff_time
	if within_obj == "runlength" or within_obj == "median_runlength"
		maxOK = cutoff_length
	end

#	require "stats_ils.rb"
	return instanceObjectives.quantile(0.9) if obj_function == "q90"
#	return instanceObjectives.median if obj_function == "median"
	return instanceObjectives.quantile(0.5) if obj_function == "median"
	return instanceObjectives.avg if obj_function == "mean"
	if obj_function == "mean1000"
		mod_obj = []
		for obj in instanceObjectives
			if obj > maxOK
				mod_obj << obj*1000 # FH: replaced maxOK by obj to enable tie breaking by solution quality (obj has a small additive term from the solution quality in there).
			else
				mod_obj << obj
			end
		end
		return mod_obj.avg
	end
	if obj_function == "mean10"
		mod_obj = []
		for obj in instanceObjectives
			if obj > maxOK
				mod_obj << obj*10 # FH: replaced maxOK by obj to enable tie breaking by solution quality (obj has a small additive term from the solution quality in there).
			else
				mod_obj << obj
			end
		end
		return mod_obj.avg
	end
	return instanceObjectives.avg if obj_function == "avg"
	if obj_function == "geomean"
		sum=0
#		puts instanceObjectives
		for obj in instanceObjectives
			sum += Math.log10(obj)
		end
		avg = sum/instanceObjectives.length
		return 10 ** avg
	end
	if obj_function == "geomean8"
		sum=0
#		puts instanceObjectives
		for obj in instanceObjectives
			sum += Math.log10(obj * (obj>maxOK ? 8 : 1))
		end
		avg = sum/instanceObjectives.length
		return 10 ** avg
	end
	if obj_function == "adj_mean"
		sum = 0
		numSucc = 0
		for obj in instanceObjectives
			if obj<maxOK
				sum += obj;
				numSucc+=1;
			else
				sum += obj;
			end
		end
		if numSucc == 0
			return sum*10
		else
			return sum/numSucc
		end
	end	
	raise "Need to implement combination of objective functions #{obj_function}."
end
