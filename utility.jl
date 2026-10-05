using Printf

# print an elapsed time in dddd:hh:mm:ss.ssssss format
function print_elapsed_time(time)
    if time <= 0
        println("Total elapsed time = 0000:00:00:0.000000")
    else
        days = Int(div(time, 86400))
        time = time - (days * 86400)
        hrs = Int(div(time, 3600))
        time = time - (hrs * 3600)
        mins = Int(div(time, 60))
        secs = time - (mins * 60)
        
        # Formatting in Julia using Printf standard library
        # days: 4 digits, zero-padded (%04d)
        # hrs: 2 digits, zero-padded (%02d)
        # mins: 2 digits, zero-padded (%02d)
        # secs: width with decimal (%09.6f)
        Printf.@printf("Total elapsed time = %04d:%02d:%02d:%09.6f\n", days, hrs, mins, secs)
    end
end
