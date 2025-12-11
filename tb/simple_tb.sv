module axi4lite_reg_station_tb;
    // DUT parameters
    parameter ADDR_WIDTH    = 32;
    parameter DATA_WIDTH    = 32;
    parameter ERR_RESP_EN   = 1 ;
    parameter IRQ_EN        = 1 ;
    parameter IRQ_HOLD_TIME = 8 ;
    parameter RST_SYNC_EN   = 1 ;

    // Ports
    logic                             aclk         ;
    logic                             aresetn      ;
    logic                             irq_o        ;

    logic [ADDR_WIDTH - 1 : 0]        s_axi_awaddr ;
    logic                             s_axi_awvalid;
    logic                             s_axi_awready;
    logic [2 : 0]                     s_axi_awprot ;
    logic [DATA_WIDTH - 1 : 0]        s_axi_wdata  ;
    logic [(DATA_WIDTH / 8) - 1 : 0]  s_axi_wstrb  ;
    logic                             s_axi_wvalid ;
    logic                             s_axi_wready ;
    logic [1 : 0]                     s_axi_bresp  ;
    logic                             s_axi_bvalid ;
    logic                             s_axi_bready ;
    logic [ADDR_WIDTH - 1 : 0]        s_axi_araddr ;
    logic                             s_axi_arvalid;
    logic                             s_axi_arready;
    logic [2 : 0]                     s_axi_arprot ;
    logic [DATA_WIDTH - 1 : 0]        s_axi_rdata  ;
    logic                             s_axi_rvalid ;
    logic                             s_axi_rready ;
    logic [1 : 0]                     s_axi_rresp  ;

    logic [ADDR_WIDTH - 1 : 0]        m_axi_awaddr ;
    logic                             m_axi_awvalid;
    logic                             m_axi_awready;
    logic [2 : 0]                     m_axi_awprot ;
    logic [DATA_WIDTH - 1 : 0]        m_axi_wdata  ;
    logic [(DATA_WIDTH / 8) - 1 : 0]  m_axi_wstrb  ;
    logic                             m_axi_wvalid ;
    logic                             m_axi_wready ;
    logic [1 : 0]                     m_axi_bresp  ;
    logic                             m_axi_bvalid ;
    logic                             m_axi_bready ;
    logic [ADDR_WIDTH - 1 : 0]        m_axi_araddr ;
    logic                             m_axi_arvalid;
    logic                             m_axi_arready;
    logic [2 : 0]                     m_axi_arprot ;
    logic [DATA_WIDTH - 1 : 0]        m_axi_rdata  ;
    logic                             m_axi_rvalid ;
    logic                             m_axi_rready ;
    logic [1 : 0]                     m_axi_rresp  ;

    localparam CLK_PERIOD = 10;
    localparam int ALIGN_BITS = $clog2(DATA_WIDTH / 8);

    logic [(DATA_WIDTH / 8) - 1 : 0] wstrb_all_ones;
    logic [(DATA_WIDTH / 8) - 1 : 0] wstrb_all_zeros;
    logic unaligned_addr;
    bit rresp_check_flag = 1'b1;
    bit bresp_check_flag = 1'b1;

    initial begin
        wstrb_all_ones  = {(DATA_WIDTH / 8){1'b1}};
        wstrb_all_zeros = {(DATA_WIDTH / 8){1'b0}};
    end

    assign unaligned_addr = ((s_axi_awvalid && (s_axi_awaddr & ((1 << ALIGN_BITS) - 1)) != 0) || (s_axi_arvalid && (s_axi_araddr & ((1 << ALIGN_BITS) - 1)) != 0));

    initial begin
        aclk = 0;
        forever begin
            #((CLK_PERIOD / 2) * 1ns) aclk = ~aclk;
        end
    end

    function automatic [ADDR_WIDTH - 1 : 0] rand_aligned_addr();
        return $urandom() & ~((DATA_WIDTH / 8) - 1);
    endfunction

    function automatic [ADDR_WIDTH - 1 : 0] rand_unaligned_addr();
        return ($urandom() & ((1 << ADDR_WIDTH) - 1)) | ($urandom() & ((1 << ALIGN_BITS) - 1) | 1);
    endfunction

    task automatic wait_cycles(input int n);
        repeat (n) begin
            @(posedge aclk);
        end
    endtask

    task automatic reset_gen(int duration);
        aresetn <= 1'b0;
        #(duration * 1ns);
        aresetn <= 1'b1;
    endtask

    task automatic reset_gen_with_delay(int duration, int delay);
        #(delay * 1ns);
        aresetn <= 1'b0;
        #(duration * 1ns);
        aresetn <= 1'b1;
    endtask

    task automatic reset_wait();
        wait(!aresetn);
        wait(aresetn);
    endtask

    task automatic axi_write(input [ADDR_WIDTH - 1 : 0] addr, input [DATA_WIDTH - 1 : 0] data, input [(DATA_WIDTH / 8) - 1 : 0] wstrb);
        s_axi_awaddr  <= addr;
        s_axi_awvalid <= 1;
        s_axi_awprot  <= '0;
        s_axi_wdata   <= data;
        s_axi_wstrb   <= wstrb;
        s_axi_wvalid  <= 1;
        s_axi_bready  <= 1;
        @(posedge aclk);
        while (!s_axi_awready) @(posedge aclk);
        s_axi_awvalid <= 0;
        @(posedge aclk);
        while (!s_axi_wready) @(posedge aclk);
        s_axi_wvalid <= 0;
        @(posedge aclk);
        while (!s_axi_bvalid) @(posedge aclk);
    endtask

    task automatic axi_read(input [ADDR_WIDTH - 1 : 0] addr);
        s_axi_araddr  <= addr;
        s_axi_arvalid <= 1;
        s_axi_arprot  <= '0;
        s_axi_rready  <= 1;
        @(posedge aclk);
        while (!s_axi_arready) @(posedge aclk);
        s_axi_arvalid <= 0;
        @(posedge aclk);
        while (!s_axi_rvalid) @(posedge aclk);
    endtask

    task automatic read_transaction(input bit unaligned_addr_flag);
        int unsigned rand_addr;

        if (!unaligned_addr_flag) begin
            rand_addr = rand_aligned_addr();
            $display("READ test: addr=%h", rand_addr);
        end else begin
            rresp_check_flag = 1'b0;
            rand_addr = rand_unaligned_addr();
            $display("READ test with unaligned address: addr=%h", rand_addr);
        end

        axi_read(rand_addr);

        if (unaligned_addr_flag && ERR_RESP_EN && s_axi_rresp !== 2'b10) begin
            $error("ERROR: Unaligned read address %h did not produce SLVERR, rresp=%b", rand_addr, s_axi_rresp);
        end
    endtask

    task automatic write_transaction(input bit unaligned_addr_flag, input bit zero_wstrb_flag);
        int unsigned rand_addr;
        int unsigned rand_data;

        rand_data = $urandom();
        rand_addr = unaligned_addr_flag ? rand_unaligned_addr() : rand_aligned_addr();
        $display("WRITE test with: addr=%h, data=%h, wstrb=%h", rand_addr, rand_data, zero_wstrb_flag ? wstrb_all_zeros : wstrb_all_ones);
        axi_write(rand_addr, rand_data, zero_wstrb_flag ? wstrb_all_zeros : wstrb_all_ones);

        if ((unaligned_addr_flag || zero_wstrb_flag) && ERR_RESP_EN && s_axi_bresp !== 2'b10) begin
            $error("ERROR: uncorrect transaction not produce SLVERR, bresp=%b", s_axi_bresp);
        end
    endtask

    initial reset_gen(2 * CLK_PERIOD);

    initial begin
        m_axi_awready = 0;
        m_axi_wready  = 0;
        m_axi_bvalid  = 0;
        m_axi_bresp   = 0;
        m_axi_arready = 0;
        m_axi_rvalid  = 0;
        m_axi_rresp   = 0;
        m_axi_rdata   = '0;
        @(posedge aresetn);

        forever begin
            @(posedge aclk);
            m_axi_awready <= 1;
            m_axi_wready <= 1;

            if (!m_axi_bvalid) begin
                if (m_axi_awvalid && m_axi_awready &&
                    m_axi_wvalid  && m_axi_wready) begin
                    m_axi_bvalid <= 1;
                    m_axi_bresp  <= 0;
                end
            end else if (m_axi_bready) begin
                m_axi_bvalid <= 0;
            end

            m_axi_arready <= 1;
            if (m_axi_arvalid && m_axi_arready) begin
                m_axi_rvalid <= 1;
                m_axi_rresp  <= 0;
                m_axi_rdata  <= m_axi_araddr ^ 32'h12345678; // deterministic random
            end

            if (m_axi_rvalid && m_axi_rready) begin
                m_axi_rvalid <= 0;
            end
        end
    end

    initial begin
        int unsigned reset_cycles;
        int rep_cnt;

        // Waiting for transition to working mode
        reset_wait();
        wait_cycles(30);

        // Random number of valid write transactions
        rep_cnt = $urandom_range(1, 30);
        repeat (rep_cnt) begin
            write_transaction(1'b0, 1'b0);
        end
        // Random number of valid read transactions
        rep_cnt = $urandom_range(1, 30);
        repeat (rep_cnt) begin
            read_transaction(1'b0);
        end
        wait_cycles(10);

        // Submitting a non-synchronous reset
        fork
            reset_gen_with_delay(2 * CLK_PERIOD, 2);
            reset_wait();
        join
        wait_cycles(3);

        // Random number of read transactions with unaligned address
        rep_cnt = $urandom_range(1, 15);
        rresp_check_flag = ERR_RESP_EN ? 1'b0 : 1'b1;
        repeat (rep_cnt) begin
            read_transaction(1'b1);
        end
        rresp_check_flag = 1'b1;
        // Random number of write transactions with unaligned address
        bresp_check_flag = ERR_RESP_EN ? 1'b0 : 1'b1;
        rep_cnt = $urandom_range(1, 15);
        repeat (rep_cnt) begin
            write_transaction(1'b1, 1'b0);
        end
        // Random number of write transactions with zero wstrb
        rep_cnt = $urandom_range(1, 15);
        repeat (rep_cnt) begin
            write_transaction(1'b0, 1'b1);
        end
        // Random number of write transactions with unaligned address and zero wstrb
        rep_cnt = $urandom_range(1, 15);
        repeat (rep_cnt) begin
            write_transaction(1'b1, 1'b1);
        end
        bresp_check_flag = 1'b1;

        // Random number of valid write transactions
        rep_cnt = $urandom_range(1, 30);
        repeat (rep_cnt) begin
            write_transaction(1'b0, 1'b0);
        end
        // Random number of valid read transactions
        rep_cnt = $urandom_range(1, 30);
        repeat (rep_cnt) begin
            read_transaction(1'b0);
        end

        // Reset during interrupt
        rresp_check_flag = ERR_RESP_EN ? 1'b0 : 1'b1;
        read_transaction(1'b1);
        reset_cycles = 2 + ($urandom % 9);
        fork
            reset_gen(2 * CLK_PERIOD);
            reset_wait();
        join
        wait_cycles(30);

        $finish();
    end

    property p_reset_hold_zero;
        @(posedge aclk)
            !aresetn |-> (
                irq_o         == 0 &&
                s_axi_awready == 1 &&
                s_axi_wready  == 1 &&
                s_axi_bresp   == 0 &&
                s_axi_bvalid  == 0 &&
                s_axi_arready == 1 &&
                s_axi_rdata   == 0 &&
                s_axi_rvalid  == 0 &&
                s_axi_rresp   == 0 &&
                m_axi_awaddr  == 0 &&
                m_axi_awvalid == 0 &&
                m_axi_awprot  == 0 &&
                m_axi_wdata   == 0 &&
                m_axi_wvalid  == 0 &&
                m_axi_wstrb   == 0 &&
                m_axi_bready  == 1 &&
                m_axi_araddr  == 0 &&
                m_axi_arvalid == 0 &&
                m_axi_arprot  == 0 &&
                m_axi_rready  == 1
            );
    endproperty

    assert property(p_reset_hold_zero)
        else $error("RESET CHECK FAILED: some signals are not zero during reset");

    property p_irq_on_unaligned;
        @(posedge aclk)
        disable iff (!aresetn)
        (IRQ_EN && ERR_RESP_EN && unaligned_addr) |-> ##1 (irq_o == 1'b1) [*IRQ_HOLD_TIME];
    endproperty

    assert property (p_irq_on_unaligned)
        else $error("ERROR: irq_o did not behave correctly for unaligned AXI address");

    property p_aw_transfer;
        @(posedge aclk)
        disable iff (!aresetn)
        (s_axi_awvalid && s_axi_awready) |-> ##1 (m_axi_awvalid && m_axi_awaddr == s_axi_awaddr && m_axi_awprot == s_axi_awprot);
    endproperty

    assert property (p_aw_transfer)
        else $error("AW CHANNEL ERROR: s->m translation incorrect");

    property p_w_transfer;
        @(posedge aclk)
        disable iff (!aresetn)
        (s_axi_wvalid && s_axi_wready) |-> ##1 (m_axi_wvalid && m_axi_wdata == s_axi_wdata && m_axi_wstrb == s_axi_wstrb);
    endproperty

    assert property (p_w_transfer)
        else $error("W CHANNEL ERROR: write data not transferred");
    
    property p_ar_transfer;
        @(posedge aclk)
        disable iff (!aresetn)
        (s_axi_arvalid && s_axi_arready) |-> ##1 (m_axi_arvalid && m_axi_araddr == s_axi_araddr && m_axi_arprot == s_axi_arprot);
    endproperty

    assert property (p_ar_transfer)
        else $error("AR CHANNEL ERROR: s->m address translation failed");

    property p_r_transfer;
        @(posedge aclk)
        disable iff (!aresetn)
        (m_axi_rvalid && m_axi_rready) |-> ##1 (s_axi_rvalid && s_axi_rdata == m_axi_rdata && (!rresp_check_flag || (s_axi_rresp == m_axi_rresp)));
    endproperty

    assert property (p_r_transfer)
        else $error("R CHANNEL ERROR: m->s read data translation failed");
    
    property p_b_transfer;
        @(posedge aclk)
        disable iff (!aresetn)
        (m_axi_bvalid && m_axi_bready) |-> ##1 (s_axi_bvalid && (!bresp_check_flag || (s_axi_bresp == m_axi_bresp)));
    endproperty

    assert property(p_b_transfer)
        else $error("B CHANNEL ERROR: write response not passed to s_axi");


    axi4lite_reg_station #(
        .ADDR_WIDTH   (ADDR_WIDTH   ),
        .DATA_WIDTH   (DATA_WIDTH   ),
        .ERR_RESP_EN  (ERR_RESP_EN  ),
        .IRQ_EN       (IRQ_EN       ),
        .IRQ_HOLD_TIME(IRQ_HOLD_TIME),
        .RST_SYNC_EN  (RST_SYNC_EN  )
    ) reg_station (
        .aclk         (aclk         ),
        .aresetn      (aresetn      ),
        .irq_o        (irq_o        ),
        .s_axi_awaddr (s_axi_awaddr ),
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_awprot (s_axi_awprot ),
        .s_axi_wdata  (s_axi_wdata  ),
        .s_axi_wstrb  (s_axi_wstrb  ),
        .s_axi_wvalid (s_axi_wvalid ),
        .s_axi_wready (s_axi_wready ),
        .s_axi_bresp  (s_axi_bresp  ),
        .s_axi_bvalid (s_axi_bvalid ),
        .s_axi_bready (s_axi_bready ),
        .s_axi_araddr (s_axi_araddr ),
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_arprot (s_axi_arprot ),
        .s_axi_rdata  (s_axi_rdata  ),
        .s_axi_rvalid (s_axi_rvalid ),
        .s_axi_rready (s_axi_rready ),
        .s_axi_rresp  (s_axi_rresp  ),
        .m_axi_awaddr (m_axi_awaddr ),
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_awready(m_axi_awready),
        .m_axi_awprot (m_axi_awprot ),
        .m_axi_wdata  (m_axi_wdata  ),
        .m_axi_wstrb  (m_axi_wstrb  ),
        .m_axi_wvalid (m_axi_wvalid ),
        .m_axi_wready (m_axi_wready ),
        .m_axi_bresp  (m_axi_bresp  ),
        .m_axi_bvalid (m_axi_bvalid ),
        .m_axi_bready (m_axi_bready ),
        .m_axi_araddr (m_axi_araddr ),
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_arready(m_axi_arready),
        .m_axi_arprot (m_axi_arprot ),
        .m_axi_rdata  (m_axi_rdata  ),
        .m_axi_rvalid (m_axi_rvalid ),
        .m_axi_rready (m_axi_rready ),
        .m_axi_rresp  (m_axi_rresp  )
    );
endmodule
