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
    Message msg;
    Message ack;
    // 0: idle, 1: send ack to satellite 2, 2: send ack to satellite 3, 3: wait for grant and send, 4: wait for ack from ground station, 
    // 5: wait for ack from satellite 2, 6: wait for ack from satellite 3, 7: ack received
    int state = 0; 
    run timer(0);
    do
    // Receive or send message (idle)
    :: state == 0 -> if
        :: isl12 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite1] Received from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 1;
            :: else -> printf("[satellite1] Dropped from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: isl13 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite1] Received from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 2;
            :: else -> printf("[satellite1] Dropped from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: buffer ? msg -> printf("[satellite1] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 3;
        fi
    // send ack to satellite 2
    :: state == 1 && len(grant_isl12) > 0 ->
        grant_isl12 ? _; buffer ! msg; printf("[satellite1] Grant isl12, ack sent\n"); state = 0; isl12 ! ack_message;
    // send ack to satellite 3
    :: state == 2 && len(grant_isl13) > 0 ->
        grant_isl13 ? _ -> buffer ! msg; printf("[satellite1] Grant isl13, ack sent\n"); state = 0; isl13 ! ack_message;
    // Wait for grant and send
    :: state == 3 -> if
        :: msg.dest == 0 && len(grant_ground1) > 0 -> grant_ground1 ? _; printf("[satellite1] Grant ground1, sending to ground\n"); state = 4; to_ground1 ! msg; timer_on[0] ! 1;
        :: msg.dest == 1 -> printf("[satellite1] Message for self, drop\n"); state = 0;
        :: msg.dest == 2 && len(grant_isl12) > 0 -> grant_isl12 ? _; printf("[satellite1] Grant isl12, sending to sat2\n"); state = 5; isl12 ! msg; timer_on[0] ! 1;
        :: msg.dest == 3 && len(grant_isl13) > 0 -> grant_isl13 ? _; printf("[satellite1] Grant isl13, sending to sat3\n"); state = 6; isl13 ! msg; timer_on[0] ! 1;
        :: else -> buffer ! msg; printf("[satellite1] No grant, re-buffer\n"); state = 0;
        fi
    // Wait for ack from ground station
    :: state == 4 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for ground ACK\n"); state = 3;
        :: to_ground1 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from ground\n"); state = 7;
        fi
    // Wait for ack from satellite 2
    :: state == 5 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for sat2 ACK\n"); state = 3;
        :: isl12 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from sat2\n"); state = 7;
        fi
    // Wait for ack from satellite 3
    :: state == 6 -> if
        :: time_out[0] ? _ -> printf("[satellite1] TIMEOUT waiting for sat3 ACK\n"); state = 3;
        :: isl13 ? ack -> timer_off[0] ! 1; printf("[satellite1] Received ACK from sat3\n"); state = 7;
        fi
    // ack received
    :: state == 7 -> if 
        :: ack.type == ACK -> printf("[satellite1] ACK received, back to idle\n"); state = 0;
        :: else -> printf("[satellite1] Not ACK, retry\n"); state = 3;
        fi
    od
}

proctype satellite2(chan buffer) {
    Message msg;
    Message ack;
    int state = 0; // 0: idle, 1: send ack to satellite 1, 2: send ack to satellite 3, 3: wait for grant and send, 4: wait for ack from ground station, 5: wait for ack from satellite 1, 6: wait for ack from satellite 3, 7: ack received
    run timer(1);
    do
    // Receive or send message (idle)
    :: state == 0 -> if
        :: isl12 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite2] Received from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 1;
            :: else -> printf("[satellite2] Dropped from isl12: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: isl23 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite2] Received from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 2;
            :: else -> printf("[satellite2] Dropped from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: buffer ? msg -> printf("[satellite2] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 3;
        fi
    // send ack to satellite 1
    :: state == 1 && len(grant_isl12) > 0 ->
        grant_isl12 ? _; buffer ! msg; printf("[satellite2] Grant isl12, ack sent\n"); state = 0; isl12 ! ack_message;
    // send ack to satellite 3
    :: state == 2 && len(grant_isl23) > 0 ->
        grant_isl23 ? _; buffer ! msg; printf("[satellite2] Grant isl23, ack sent\n"); state = 0; isl23 ! ack_message;
    // Wait for grant and send
    :: state == 3 -> if
        :: msg.dest == 0 && len(grant_ground2) > 0 -> grant_ground2 ? _; printf("[satellite2] Grant ground2, sending to ground\n"); state = 4; to_ground2 ! msg; timer_on[1] ! 1;
        :: msg.dest == 1 && len(grant_isl12) > 0 -> grant_isl12 ? _; printf("[satellite2] Grant isl12, sending to sat1\n"); state = 5; isl12 ! msg; timer_on[1] ! 1;
        :: msg.dest == 2 -> printf("[satellite2] Message for self, drop\n"); state = 0;
        :: msg.dest == 3 && len(grant_isl23) > 0 -> grant_isl23 ? _; printf("[satellite2] Grant isl23, sending to sat3\n"); state = 6; isl23 ! msg; timer_on[1] ! 1;
        :: else -> buffer ! msg; printf("[satellite2] No grant, re-buffer\n"); state = 0;
        fi
    // Wait for ack from ground station
    :: state == 4 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for ground ACK\n"); state = 3;
        :: to_ground2 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from ground\n"); state = 7;
        fi
    // Wait for ack from satellite 1
    :: state == 5 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for sat1 ACK\n"); state = 3;
        :: isl12 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from sat1\n"); state = 7;
        fi
    // Wait for ack from satellite 3
    :: state == 6 -> if
        :: time_out[1] ? _ -> printf("[satellite2] TIMEOUT waiting for sat3 ACK\n"); state = 3;
        :: isl23 ? ack -> timer_off[1] ! 1; printf("[satellite2] Received ACK from sat3\n"); state = 7;
        fi
    // ack received
    :: state == 7 -> if 
        :: ack.type == ACK -> printf("[satellite2] ACK received, back to idle\n"); state = 0;
        :: else -> printf("[satellite2] Not ACK, retry\n"); state = 3;
        fi
    od
}

proctype satellite3(chan buffer) {
    Message msg;
    Message ack;
    int state = 0; // 0: idle, 1: send ack to satellite 1, 2: send ack to satellite 2, 3: wait for grant and send, 4: wait for ack from ground station, 5: wait for ack from satellite 1, 6: wait for ack from satellite 2, 7: ack received
    run timer(2);
    do
    // Receive or send message (idle)
    :: state == 0 -> if
        :: isl13 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite3] Received from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 1;
            :: else -> printf("[satellite3] Dropped from isl13: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: isl23 ? msg -> if
            :: len(buffer) < BUFFER_SIZE -> printf("[satellite3] Received from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 2;
            :: else -> printf("[satellite3] Dropped from isl23: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload);
            fi
        :: buffer ? msg -> printf("[satellite3] Buffer pop: type=%d, src=%d, dest=%d, payload=%d\n", msg.type, msg.src, msg.dest, msg.payload); state = 3;
        fi
    // send ack to satellite 1
    :: state == 1 && len(grant_isl13) > 0 ->
        grant_isl13 ? _; buffer ! msg; printf("[satellite3] Grant isl13, ack sent\n"); state = 0; isl13 ! ack_message;
    // send ack to satellite 2
    :: state == 2 && len(grant_isl23) > 0 ->
        grant_isl23 ? _; buffer ! msg; printf("[satellite3] Grant isl23, ack sent\n"); state = 0; isl23 ! ack_message;
    // Wait for grant and send
    :: state == 3 -> if
        :: msg.dest == 0 && len(grant_ground3) > 0 -> grant_ground3 ? _; printf("[satellite3] Grant ground3, sending to ground\n"); state = 4; to_ground3 ! msg; timer_on[2] ! 1;
        :: msg.dest == 1 && len(grant_isl13) > 0 -> grant_isl13 ? _; printf("[satellite3] Grant isl13, sending to sat1\n"); state = 5; isl13 ! msg; timer_on[2] ! 1;
        :: msg.dest == 2 && len(grant_isl23) > 0 -> grant_isl23 ? _; printf("[satellite3] Grant isl23, sending to sat2\n"); state = 6; isl23 ! msg; timer_on[2] ! 1;
        :: msg.dest == 3 -> printf("[satellite3] Message for self, drop\n"); state = 0;
        :: else -> buffer ! msg; printf("[satellite3] No grant, re-buffer\n"); state = 0;
        fi
    // Wait for ack from ground station
    :: state == 4 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for ground ACK\n"); state = 3;
        :: to_ground3 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from ground\n"); state = 7;
        fi
    // Wait for ack from satellite 1
    :: state == 5 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for sat1 ACK\n"); state = 3;
        :: isl13 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from sat1\n"); state = 7;
        fi
    // Wait for ack from satellite 2
    :: state == 6 -> if
        :: time_out[2] ? _ -> printf("[satellite3] TIMEOUT waiting for sat2 ACK\n"); state = 3;
        :: isl23 ? ack -> timer_off[2] ! 1; printf("[satellite3] Received ACK from sat2\n"); state = 7;
        fi
    // ack received
    :: state == 7 -> if 
        :: ack.type == ACK -> printf("[satellite3] ACK received, back to idle\n"); state = 0;
        :: else -> printf("[satellite3] Not ACK, retry\n"); state = 3;
        fi
    od
}

init {
    chan satellite1_buffer = [5] of { Message };
    chan satellite2_buffer = [5] of { Message };
    chan satellite3_buffer = [5] of { Message };
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
    //
    Message sample2;
    sample2.type = TELEMETRY;
    sample2.src = 2;
    sample2.dest = 3;
    sample2.payload = 0;
    satellite2_buffer ! sample2
    // run processes
    run timeKeeper();
    run coordinator();
    run satellite1(satellite1_buffer);
    run satellite2(satellite2_buffer);
    run satellite3(satellite3_buffer);
    run groundStation();
}
