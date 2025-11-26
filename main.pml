#define BUFFER_SIZE 5;

chan slot_signal = [0] of { byte };

// Message
mtype = { TELEMETRY, COMMAND, IMAGE, ACK };
typedef Message {
    mtype type;
    byte  src; // 0: ground, 1: satellite 1, 2: satellite 2, 3: satellite 3
    byte  dest; // 0: ground, 1: satellite 1, 2: satellite 2, 3: satellite 3
    byte  payload;
}
Message ack_message;

// grant channels
chan grant_ground1 = [1] of {bit}
chan grant_ground2 = [1] of {bit}
chan grant_ground3 = [1] of {bit}
chan grant_isl12 = [1] of {bit}
chan grant_isl13 = [1] of {bit}
chan grant_isl23 = [1] of {bit}

// Communication channels
chan to_ground1 = [0] of { Message }
chan to_ground2 = [0] of { Message }
chan to_ground3 = [0] of { Message }
chan isl12 = [0] of { Message }
chan isl13 = [0] of { Message }
chan isl23 = [0] of { Message }

// Timer channels
chan timer_on[3] = [0] of { bit }
chan timer_off[3] = [0] of { bit }
chan time_out[3] = [0] of { bit }

// slot changed notify
chan slot_changed1 = [13] of { bit }
chan slot_changed2 = [13] of { bit }
chan slot_changed3 = [13] of { bit }

// satellite states
// 0: idle, 1: send ack to satellite 2, 2: send ack to satellite 3, 3: wait for grant and send, 4: wait for ack from ground station, 
// 5: wait for ack from satellite 2, 6: wait for ack from satellite 3, 7: ack received
int state1 = 0;
int state2 = 0;
int state3 = 0;

// batteries
byte battery1 = 100;
byte battery2 = 100;
byte battery3 = 100;

// Buffer
chan satellite1_buffer = [5] of { Message };
chan satellite2_buffer = [5] of { Message };
chan satellite3_buffer = [5] of { Message };


proctype timeKeeper() {
    byte current_slot = 0;
    byte timer = 0;
    do
    :: timer >= 7 -> if
        :: current_slot < 7 -> current_slot = current_slot + 1;
        :: current_slot >= 7 -> current_slot = 0;
        fi
        printf("[timeKeeper] current_slot = %d\n", current_slot);
        slot_signal ! current_slot;
        slot_changed1 ! 1;
        slot_changed2 ! 1;
        slot_changed3 ! 1;
        timer = 0;
    :: else -> timer++;
    od
}

proctype coordinator() {
    byte slot = 0;
    do 
    :: slot_signal ? slot -> printf("[coordinator] Received slot = %d\n", slot); atomic{if
        :: len(grant_ground1) > 0 -> grant_ground1 ? _;
        :: len(grant_ground2) > 0 -> grant_ground2 ? _;
        :: len(grant_ground3) > 0 -> grant_ground3 ? _;
        :: len(grant_isl12) > 0 -> grant_isl12 ? _;
        :: len(grant_isl23) > 0 -> grant_isl23 ? _;
        :: len(grant_isl13) > 0 -> grant_isl13 ? _;
        :: else -> skip;
        fi}
    :: slot == 0 && len(grant_ground1) == 0 ->
        grant_ground1 ! 1;
        printf("[coordinator] Grant to ground1\n")
    :: slot == 1 && len(grant_ground2) == 0 ->
        grant_ground2 ! 1;
        printf("[coordinator] Grant to ground2\n")
    :: slot == 2 && len(grant_ground3) == 0 ->
        grant_ground3 ! 1;
        printf("[coordinator] Grant to ground3\n")
    :: slot == 4 && len(grant_isl12) == 0 ->
        grant_isl12 ! 1;
        printf("[coordinator] Grant to isl12\n")
    :: slot == 5 && len(grant_isl23) == 0 ->
        grant_isl23 ! 1;
        printf("[coordinator] Grant to isl23\n")
    :: slot == 6 && len(grant_isl13) == 0 ->
        grant_isl13 ! 1;
        printf("[coordinator] Grant to isl13\n")
    od 
}

proctype groundStation() {
    Message msg;
    // counters for received messages from each satellite
    int count_received_messages[3];
    atomic {
        count_received_messages[0] = 0;
        count_received_messages[1] = 0;
        count_received_messages[2] = 0;
    }
    byte state = 0; // 0: idle, 1: received from satellite 1, 2: received from satellite 2, 3: received from satellite 3
    do
    :: state == 0 -> if 
        :: to_ground1 ? msg ->
            printf("[groundStation] Received message from satellite 1: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            state = 1;
        :: to_ground2 ? msg ->
            printf("[groundStation] Received message from satellite 2: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            state = 2;
        :: to_ground3 ? msg ->
            printf("[groundStation] Received message from satellite 3: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            state = 3;
        fi
    :: state == 1 && len(grant_ground1) > 0 -> grant_ground1 ? _; count_received_messages[0]++; printf("[groundStation] Grant for satellite 1, count=%d\n", count_received_messages[0]); state = 0; to_ground1 ! ack_message; printf("[groundStation] Sent ACK to satellite 1\n");
    :: state == 2 && len(grant_ground2) > 0 -> grant_ground2 ? _; count_received_messages[1]++; printf("[groundStation] Grant for satellite 2, count=%d\n", count_received_messages[1]); state = 0; to_ground2 ! ack_message; printf("[groundStation] Sent ACK to satellite 2\n");
    :: state == 3 && len(grant_ground3) > 0 -> grant_ground3 ? _; count_received_messages[2]++; printf("[groundStation] Grant for satellite 3, count=%d\n", count_received_messages[2]); state = 0; to_ground3 ! ack_message; printf("[groundStation] Sent ACK to satellite 3\n");
    od
}

proctype timer(byte id) {
    bit status = 0; // 0: off, 1: on
    do
    :: timer_on[id] ? _ -> status = 1; printf("[timer %d] ON\n", id);
    :: timer_off[id] ? _ -> status = 0; printf("[timer %d] OFF\n", id);
    :: status == 1 -> if
        :: time_out[id] ! 1 -> status = 0; printf("[timer %d] TIMEOUT\n", id);
        :: true -> skip;
        fi
    od
}

proctype satellite1(chan buffer) {
    bool safe_mode = false;
    Message msg;
    Message ack;
    // 0: idle, 1: send ack to satellite 2, 2: send ack to satellite 3, 3: wait for grant and send, 4: wait for ack from ground station, 
    // 5: wait for ack from satellite 2, 6: wait for ack from satellite 3, 7: ack received
    run timer(0);
    do
    // charge battery1
    :: len(slot_changed1) > 0 -> slot_changed1 ? _; if
        :: battery1 + 8 >= 100 -> battery1 = 100;
        :: else -> battery1 = battery1 + 8;
        fi; 
        printf("[satellite1] battery1=%d\n", battery1); if
        :: battery1 > 20 -> safe_mode = false; printf("[satellite1] Safe mode off\n");
        :: else -> skip;
        fi
    // Receive or send message (idle)
    :: state1 == 0 -> if
        ::  battery1 >= 6 -> if
            :: isl12 ? msg -> battery1 = battery1 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite1] Received from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state1 = 1;
                :: else -> printf("[satellite1] Dropped from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery1 >= 6 -> if
            :: isl13 ? msg -> battery1 = battery1 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite1] Received from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state1 = 2;
                :: else -> printf("[satellite1] Dropped from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery1 >= 10 && len(buffer) > 0 -> buffer ? msg; printf("[satellite1] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state1 = 3;
        :: else -> skip;
        fi
    // send ack to satellite 2
    :: state1 == 1 && len(grant_isl12) > 0 ->
        grant_isl12 ? _; buffer ! msg; printf("[satellite1] Grant isl12, ack sent\n"); state1 = 8; isl12 ! ack_message; battery1--;
    // send ack to satellite 3
    :: state1 == 2 && len(grant_isl13) > 0 ->
        grant_isl13 ? _ -> buffer ! msg; printf("[satellite1] Grant isl13, ack sent\n"); state1 = 8; isl13 ! ack_message; battery1--;
    // Wait for grant and send
    :: state1 == 3 -> if
        :: msg.dest == 0 && len(grant_ground1) > 0 && battery1 >= 20 -> grant_ground1 ? _; printf("[satellite1] Grant ground1, sending to ground\n"); state1 = 4; to_ground1 ! msg; timer_on[0] ! 1; battery1 = battery1 - 15;
        :: msg.dest == 1 -> printf("[satellite1] Message for self, drop\n"); state1 = 0;
        :: msg.dest == 2 && len(grant_isl12) > 0 && battery1 >= 20 -> grant_isl12 ? _; printf("[satellite1] Grant isl12, sending to sat2\n"); state1 = 5; isl12 ! msg; timer_on[0] ! 1; battery1 = battery1 - 10;
        :: msg.dest == 3 && len(grant_isl13) > 0 && battery1 >= 20 -> grant_isl13 ? _; printf("[satellite1] Grant isl13, sending to sat3\n"); state1 = 6; isl13 ! msg; timer_on[0] ! 1; battery1 = battery1 - 10;
        :: else -> buffer ! msg; printf("[satellite1] No grant, re-buffer\n"); state1 = 0;
        fi
    // Wait for ack from ground station
    :: state1 == 4 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for ground ACK\n"); state1 = 3;
        :: to_ground1 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from ground\n"); state1 = 7; battery1--;
        fi
    // Wait for ack from satellite 2
    :: state1 == 5 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for sat2 ACK\n"); state1 = 3;
        :: isl12 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from sat2\n"); state1 = 7; battery1--;
        fi
    // Wait for ack from satellite 3
    :: state1 == 6 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for sat3 ACK\n"); state1 = 3;
        :: isl13 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from sat3\n"); state1 = 7; battery1--;
        fi
    // ack received
    :: state1 == 7 -> if 
        :: ack.type == ACK -> printf("[satellite1] ACK received, back to idle\n"); state1 = 8;
        :: else -> printf("[satellite1] Not ACK, retry\n"); state1 = 3;
        fi
    // battery1 check
    :: state1 == 8 -> if
        :: battery1 < 10 -> safe_mode = true; printf("[satellite1] Safe mode on\n");
        :: else -> skip
        fi
    od
}

proctype satellite2(chan buffer) {
    bool safe_mode = false;
    Message msg;
    Message ack;
    run timer(1);
    do
    // charge battery2
    :: len(slot_changed2) > 0 -> slot_changed2 ? _; if
        :: battery2 + 8 >= 100 -> battery2 = 100;
        :: else -> battery2 = battery2 + 8;
        fi;
        printf("[satellite2] battery2=%d\n", battery2); if
        :: battery2 > 20 -> safe_mode = false; printf("[satellite2] Safe mode off\n");
        :: else -> skip;
        fi
    // Receive or send message (idle)
    :: state2 == 0 -> if
        :: battery2 >= 6 -> if
            :: isl12 ? msg -> battery2 = battery2 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite2] Received from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state2 = 1;
                :: else -> printf("[satellite2] Dropped from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery2 >= 6 -> if
            :: isl23 ? msg -> battery2 = battery2 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite2] Received from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state2 = 2;
                :: else -> printf("[satellite2] Dropped from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery2 >= 10 && len(buffer) > 0 -> buffer ? msg; printf("[satellite2] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state2 = 3;
        :: else -> skip;
        fi
    // send ack to satellite 1
    :: state2 == 1 && len(grant_isl12) > 0 ->
        grant_isl12 ? _; buffer ! msg; printf("[satellite2] Grant isl12, ack sent\n"); state2 = 8; isl12 ! ack_message; battery2--;
    // send ack to satellite 3
    :: state2 == 2 && len(grant_isl23) > 0 ->
        grant_isl23 ? _; buffer ! msg; printf("[satellite2] Grant isl23, ack sent\n"); state2 = 8; isl23 ! ack_message; battery2--;
    // Wait for grant and send
    :: state2 == 3 -> if
        :: msg.dest == 0 && len(grant_ground2) > 0 && battery2 >= 20 -> grant_ground2 ? _; printf("[satellite2] Grant ground2, sending to ground\n"); state2 = 4; to_ground2 ! msg; timer_on[1] ! 1; battery2 = battery2 - 15;
        :: msg.dest == 1 && len(grant_isl12) > 0 && battery2 >= 20 -> grant_isl12 ? _; printf("[satellite2] Grant isl12, sending to sat1\n"); state2 = 5; isl12 ! msg; timer_on[1] ! 1; battery2 = battery2 - 10;
        :: msg.dest == 2 -> printf("[satellite2] Message for self, drop\n"); state2 = 0;
        :: msg.dest == 3 && len(grant_isl23) > 0 && battery2 >= 20 -> grant_isl23 ? _; printf("[satellite2] Grant isl23, sending to sat3\n"); state2 = 6; isl23 ! msg; timer_on[1] ! 1; battery2 = battery2 - 10;
        :: else -> buffer ! msg; printf("[satellite2] No grant, re-buffer\n"); state2 = 0;
        fi
    // Wait for ack from ground station
    :: state2 == 4 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for ground ACK\n"); state2 = 3;
        :: to_ground2 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from ground\n"); state2 = 7; battery2--;
        fi
    // Wait for ack from satellite 1
    :: state2 == 5 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for sat1 ACK\n"); state2 = 3;
        :: isl12 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from sat1\n"); state2 = 7; battery2--;
        fi
    // Wait for ack from satellite 3
    :: state2 == 6 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for sat3 ACK\n"); state2 = 3;
        :: isl23 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from sat3\n"); state2 = 7; battery2--;
        fi
    // ack received
    :: state2 == 7 -> if
        :: ack.type == ACK -> printf("[satellite2] ACK received, back to idle\n"); state2 = 8;
        :: else -> printf("[satellite2] Not ACK, retry\n"); state2 = 3;
        fi
    // battery2 check
    :: state2 == 8 -> if
        :: battery2 < 10 -> safe_mode = true; printf("[satellite2] Safe mode on\n");
        :: else -> skip
        fi
    od
}

proctype satellite3(chan buffer) {
    bool safe_mode = false;
    Message msg;
    Message ack;
    run timer(2);
    do
    // charge battery3
    :: len(slot_changed3) > 0 -> slot_changed3 ? _; if
        :: battery3 + 8 >= 100 -> battery3 = 100;
        :: else -> battery3 = battery3 + 8;
        fi;
        printf("[satellite3] battery3=%d\n", battery3); if
        :: battery3 > 20 -> safe_mode = false; printf("[satellite3] Safe mode off\n");
        :: else -> skip;
        fi
    // Receive or send message (idle)
    :: state3 == 0 -> if
        :: battery3 >= 6 -> if
            :: isl13 ? msg -> battery3 = battery3 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite3] Received from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state3 = 1;
                :: else -> printf("[satellite3] Dropped from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery3 >= 6 -> if
            :: isl23 ? msg -> battery3 = battery3 - 5; if
                :: len(buffer) < BUFFER_SIZE -> printf("[satellite3] Received from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state3 = 2;
                :: else -> printf("[satellite3] Dropped from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
                fi
            :: true -> skip;
            fi
        :: battery3 >= 10 && len(buffer) > 0 -> buffer ? msg; printf("[satellite3] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state3 = 3;
        :: else -> skip;
        fi
    // send ack to satellite 1
    :: state3 == 1 && len(grant_isl13) > 0 ->
        grant_isl13 ? _; buffer ! msg; printf("[satellite3] Grant isl13, ack sent\n"); state3 = 8; isl13 ! ack_message; battery3--;
    // send ack to satellite 2
    :: state3 == 2 && len(grant_isl23) > 0 ->
        grant_isl23 ? _; buffer ! msg; printf("[satellite3] Grant isl23, ack sent\n"); state3 = 8; isl23 ! ack_message; battery3--;
    // Wait for grant and send
    :: state3 == 3 -> if
        :: msg.dest == 0 && len(grant_ground3) > 0 && battery3 >= 20 -> grant_ground3 ? _; printf("[satellite3] Grant ground3, sending to ground\n"); state3 = 4; to_ground3 ! msg; timer_on[2] ! 1; battery3 = battery3 - 15;
        :: msg.dest == 1 && len(grant_isl13) > 0 && battery3 >= 20 -> grant_isl13 ? _; printf("[satellite3] Grant isl13, sending to sat1\n"); state3 = 5; isl13 ! msg; timer_on[2] ! 1; battery3 = battery3 - 10;
        :: msg.dest == 2 && len(grant_isl23) > 0 && battery3 >= 20 -> grant_isl23 ? _; printf("[satellite3] Grant isl23, sending to sat2\n"); state3 = 6; isl23 ! msg; timer_on[2] ! 1; battery3 = battery3 - 10;
        :: msg.dest == 3 -> printf("[satellite3] Message for self, drop\n"); state3 = 0;
        :: else -> buffer ! msg; printf("[satellite3] No grant, re-buffer\n"); state3 = 0;
        fi
    // Wait for ack from ground station
    :: state3 == 4 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for ground ACK\n"); state3 = 3;
        :: to_ground3 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from ground\n"); state3 = 7;
        fi
    // Wait for ack from satellite 1
    :: state3 == 5 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for sat1 ACK\n"); state3 = 3;
        :: isl13 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from sat1\n"); state3 = 7;
        fi
    // Wait for ack from satellite 2
    :: state3 == 6 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for sat2 ACK\n"); state3 = 3;
        :: isl23 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from sat2\n"); state3 = 7;
        fi
    // ack received
    :: state3 == 7 -> if 
        :: ack.type == ACK -> printf("[satellite3] ACK received, back to idle\n"); state3 = 8;
        :: else -> printf("[satellite3] Not ACK, retry\n"); state3 = 3;
        fi
    // battery3 check
    :: state3 == 8 -> if
        :: battery3 < 10 -> safe_mode = true; printf("[satellite3] Safe mode on\n");
        :: else -> skip
        fi
    od
}

init {
    // ack
    ack_message.type = ACK;
    ack_message.src = 0;
    ack_message.dest = 0;
    ack_message.payload = 0;
    // init buffer for satellite 1
    Message sample1;
    sample1.type = TELEMETRY;
    sample1.src = 1;
    sample1.dest = 0;
    sample1.payload = 0;
    satellite1_buffer ! sample1
    satellite1_buffer ! sample1
    // drop scenario
    Message sample2;
    sample2.type = TELEMETRY;
    sample2.src = 2;
    sample2.dest = 1;
    sample2.payload = 0;
    satellite2_buffer ! sample2;
    satellite2_buffer ! sample2;
    satellite2_buffer ! sample2;
    satellite2_buffer ! sample2;
    satellite2_buffer ! sample2;
    // fill satellite 3 buffer
    Message sample3;
    sample3.type = TELEMETRY;
    sample3.src = 3;
    sample3.dest = 1;
    sample3.payload = 0;
    satellite3_buffer ! sample3;
    // run processes
    run timeKeeper();
    run coordinator();
    run satellite1(satellite1_buffer);
    run satellite2(satellite2_buffer);
    run satellite3(satellite3_buffer);
    run groundStation();
}

ltl no_interference { [] !((state1 == 4 && state2 == 4) || (state1 == 4 && state3 == 4) || (state3 == 4 && state2 == 4)) }
ltl no_send_low_battery1 { [] !(((state1 == 4) && (battery1 < 5)) || ((state1 == 5 || state1 == 6) && (battery1 < 10)))}
ltl no_send_low_battery2 { [] !(((state2 == 4) && (battery2 < 5)) || ((state2 == 5 || state2 == 6) && (battery2 < 10))) }
ltl no_send_low_battery3 { [] !(((state3 == 4) && (battery3 < 5)) || ((state3 == 5 || state3 == 6) && (battery3 < 10))) }
ltl no_overflow { [] (len(satellite1_buffer) <= 5 && len(satellite2_buffer) <= 5 && len(satellite3_buffer) <= 5) }
ltl eventual_processing { [] <> ((len(satellite1_buffer) == 0 && len(satellite2_buffer) == 0 && len(satellite3_buffer) == 0)) }
ltl eventual_access_ground {
    [] ((len(grant_ground1) == 0 -> <> len(grant_ground1) > 0) &&
        (len(grant_ground2) == 0 -> <> len(grant_ground2) > 0) &&
        (len(grant_ground3) == 0 -> <> len(grant_ground3) > 0))
}
