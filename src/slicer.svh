module axi4lite_reg_station #(
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32
) (
    input  logic                             aclk         ,
    input  logic                             aresetn      ,
    input  logic                             err_write_i  ,
    input  logic                             err_read_i   ,

    // AXI4-Lite slave port
    input  logic [ADDR_WIDTH - 1 : 0]        s_axi_awaddr ,
    input  logic                             s_axi_awvalid,
    output logic                             s_axi_awready,
    input  logic [2 : 0]                     s_axi_awprot ,

    input  logic [DATA_WIDTH - 1 : 0]        s_axi_wdata  ,
    input  logic [(DATA_WIDTH / 8) - 1 : 0]  s_axi_wstrb  ,
    input  logic                             s_axi_wvalid ,
    output logic                             s_axi_wready ,

    output logic [1 : 0]                     s_axi_bresp  ,
    output logic                             s_axi_bvalid ,
    input  logic                             s_axi_bready ,

    input  logic [ADDR_WIDTH - 1 : 0]        s_axi_araddr ,
    input  logic                             s_axi_arvalid,
    output logic                             s_axi_arready,
    input  logic [2 : 0]                     s_axi_arprot ,

    output logic [DATA_WIDTH - 1 : 0]        s_axi_rdata  ,
    output logic                             s_axi_rvalid ,
    input  logic                             s_axi_rready ,
    output logic [1 : 0]                     s_axi_rresp  ,

    // AXI4-Lite master port
    output logic [ADDR_WIDTH - 1 : 0]        m_axi_awaddr ,
    output logic                             m_axi_awvalid,
    input  logic                             m_axi_awready,
    output logic [2 : 0]                     m_axi_awprot ,

    output logic [DATA_WIDTH - 1 : 0]        m_axi_wdata  ,
    output logic [(DATA_WIDTH / 8) - 1 : 0]  m_axi_wstrb  ,
    output logic                             m_axi_wvalid ,
    input  logic                             m_axi_wready ,

    input  logic [1 : 0]                     m_axi_bresp  ,
    input  logic                             m_axi_bvalid ,
    output logic                             m_axi_bready ,

    output logic [ADDR_WIDTH - 1 : 0]        m_axi_araddr ,
    output logic                             m_axi_arvalid,
    input  logic                             m_axi_arready,
    output logic [2 : 0]                     m_axi_arprot ,

    input  logic [DATA_WIDTH - 1 : 0]        m_axi_rdata  ,
    input  logic                             m_axi_rvalid ,
    output logic                             m_axi_rready ,
    input  logic [1 : 0]                     m_axi_rresp
);
    reg [ADDR_WIDTH - 1 : 0]       aw_addr_0      ;
    reg [ADDR_WIDTH - 1 : 0]       aw_addr_1      ;
    reg [2 : 0]                    aw_prot_0      ;
    reg [2 : 0]                    aw_prot_1      ;
    reg [1 : 0]                    aw_fifo_status ;
    reg                            aw_read        ;
    reg                            aw_write       ;

    reg [DATA_WIDTH - 1 : 0]       w_data_0      ;
    reg [DATA_WIDTH - 1 : 0]       w_data_1      ;
    reg [(DATA_WIDTH / 8) - 1 : 0] w_strb_0      ;
    reg [(DATA_WIDTH / 8) - 1 : 0] w_strb_1      ;
    reg [1 : 0]                    w_fifo_status ;
    reg                            w_read        ;
    reg                            w_write       ;

    reg [1 : 0]                    b_resp_0      ;
    reg [1 : 0]                    b_resp_1      ;
    reg [1 : 0]                    b_fifo_status ;
    reg                            b_read        ;
    reg                            b_write       ;

    reg [ADDR_WIDTH - 1 : 0]       ar_addr_0     ;
    reg [ADDR_WIDTH - 1 : 0]       ar_addr_1     ;
    reg [2 : 0]                    ar_prot_0     ;
    reg [2 : 0]                    ar_prot_1     ;
    reg [1 : 0]                    ar_fifo_status;
    reg                            ar_read       ;
    reg                            ar_write      ;

    reg [DATA_WIDTH - 1 : 0]       r_data_0      ;
    reg [DATA_WIDTH - 1 : 0]       r_data_1      ;
    reg [1 : 0]                    r_resp_0      ;
    reg [1 : 0]                    r_resp_1      ;
    reg [1 : 0]                    r_fifo_status ;
    reg                            r_read        ;
    reg                            r_write       ;

    assign aw_write_flag = s_axi_awvalid & s_axi_awready;
    assign aw_read_flag  = m_axi_awvalid & m_axi_awready;
    assign aw_empty = (aw_fifo_status == 0);
    assign aw_full  = aw_fifo_status[1];

    assign w_write_flag = s_axi_wvalid & s_axi_wready;
    assign w_read_flag  = m_axi_wvalid & m_axi_wready;
    assign w_empty = (w_fifo_status == 0);
    assign w_full  = w_fifo_status[1];

    assign b_write_flag = m_axi_bvalid & m_axi_bready;
    assign b_read_flag  = s_axi_bvalid & s_axi_bready;
    assign b_empty = (b_fifo_status == 0);
    assign b_full  = b_fifo_status[1];

    assign ar_write_flag = s_axi_arvalid & s_axi_arready;
    assign ar_read_flag  = m_axi_arvalid & m_axi_arready;
    assign ar_empty = (ar_fifo_status == 0);
    assign ar_full  = ar_fifo_status[1];

    assign r_write_flag = m_axi_rvalid & m_axi_rready;
    assign r_read_flag  = s_axi_rvalid & s_axi_rready;
    assign r_empty = (r_fifo_status == 0);
    assign r_full  = r_fifo_status[1];

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_read <= 1'b0;
        end else if (aw_read_flag) begin
            aw_read <= ~aw_read;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_read <= 1'b0;
        end else if (w_read_flag) begin
            w_read <= ~w_read;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_read <= 1'b0;
        end else if (b_read_flag) begin
            b_read <= ~b_read;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_read <= 1'b0;
        end else if (ar_read_flag) begin
            ar_read <= ~ar_read;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_read <= 1'b0;
        end else if (r_read_flag) begin
            r_read <= ~r_read;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_write <= 1'b0;
        end else if (aw_write_flag) begin
            aw_write <= ~aw_write;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_write <= 1'b0;
        end else if (w_write_flag) begin
            w_write <= ~w_write;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_write <= 1'b0;
        end else if (b_write_flag) begin
            b_write <= ~b_write;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_write <= 1'b0;
        end else if (ar_write_flag) begin
            ar_write <= ~ar_write;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_write <= 1'b0;
        end else if (r_write_flag) begin
            r_write <= ~r_write;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_fifo_status <= 2'b0;
        end else if (aw_write_flag & ~aw_read_flag) begin
	  	    aw_fifo_status <= aw_fifo_status + 1'b1;
	  	end else if (~aw_write_flag & aw_read_flag) begin
	  	    aw_fifo_status <= aw_fifo_status - 1'b1;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_fifo_status <= 2'b0;
        end else if (w_write_flag & ~w_read_flag) begin
	  	    w_fifo_status <= w_fifo_status + 1'b1;
	  	end else if (~w_write_flag & w_read_flag) begin
	  	    w_fifo_status <= w_fifo_status - 1'b1;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_fifo_status <= 2'b0;
        end else if (b_write_flag & ~b_read_flag) begin
	  	    b_fifo_status <= b_fifo_status + 1'b1;
	  	end else if (~b_write_flag & b_read_flag) begin
	  	    b_fifo_status <= b_fifo_status - 1'b1;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_fifo_status <= 2'b0;
        end else if (ar_write_flag & ~ar_read_flag) begin
	  	    ar_fifo_status <= ar_fifo_status + 1'b1;
	  	end else if (~ar_write_flag & ar_read_flag) begin
	  	    ar_fifo_status <= ar_fifo_status - 1'b1;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_fifo_status <= 2'b0;
        end else if (r_write_flag & ~r_read_flag) begin
	  	    r_fifo_status <= r_fifo_status + 1'b1;
	  	end else if (~r_write_flag & r_read_flag) begin
	  	    r_fifo_status <= r_fifo_status - 1'b1;
	  	end
    end
    
    assign s_axi_awready = ~aw_full;
    assign s_axi_wready  = ~w_full ;
    assign m_axi_bready  = ~b_full ;
    assign s_axi_arready = ~ar_full;
    assign m_axi_rready  = ~r_full ;

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            m_axi_awvalid <= 1'b0;
        end else if ((aw_fifo_status == 1) & aw_read_flag & ~aw_write_flag) begin
            m_axi_awvalid <= 1'b0;
        end else if (aw_empty & aw_write_flag & ~aw_read_flag) begin
            m_axi_awvalid <= 1'b1;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            m_axi_wvalid <= 1'b0;
        end else if ((w_fifo_status == 1) & w_read_flag & ~w_write_flag) begin
            m_axi_wvalid <= 1'b0;
        end else if (w_empty & w_write_flag & ~w_read_flag) begin
            m_axi_wvalid <= 1'b1;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_bvalid <= 1'b0;
        end else if ((b_fifo_status == 1) & b_read_flag & ~b_write_flag) begin
            s_axi_bvalid <= 1'b0;
        end else if (b_empty & b_write_flag & ~b_read_flag) begin
            s_axi_bvalid <= 1'b1;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            m_axi_arvalid <= 1'b0;
        end else if ((ar_fifo_status == 1) & ar_read_flag & ~ar_write_flag) begin
            m_axi_arvalid <= 1'b0;
        end else if (ar_empty & ar_write_flag & ~ar_read_flag) begin
            m_axi_arvalid <= 1'b1;
        end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_rvalid <= 1'b0;
        end else if ((r_fifo_status == 1) & r_read_flag & ~r_write_flag) begin
            s_axi_rvalid <= 1'b0;
        end else if (r_empty & r_write_flag & ~r_read_flag) begin
            s_axi_rvalid <= 1'b1;
        end
    end
    
    assign m_axi_awaddr = aw_read ? aw_addr_1 : aw_addr_0;
    assign m_axi_awprot = aw_read ? aw_prot_1 : aw_prot_0;
    assign m_axi_wdata  = w_read  ? w_data_1  : w_data_0 ;
    assign m_axi_wstrb  = w_read  ? w_strb_1  : w_strb_0 ;
    assign s_axi_bresp  = b_read  ? b_resp_1  : b_resp_0 ;
    assign m_axi_araddr = ar_read ? ar_addr_1 : ar_addr_0;
    assign m_axi_arprot = ar_read ? ar_prot_1 : ar_prot_0;
    assign m_axi_rdata  = r_read  ? r_data_1  : r_data_0 ;
    assign s_axi_rresp  = r_read  ? r_resp_1  : r_resp_0 ;

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_addr_0 <= {ADDR_WIDTH{1'b0}};
            aw_prot_0 <= 3'b0;
        end else if (aw_write_flag & ~aw_write) begin
	  	    aw_addr_0 <= s_axi_awaddr;
            aw_prot_0 <= s_axi_awprot;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_data_0 <= {DATA_WIDTH{1'b0}};
            w_strb_0 <= {(DATA_WIDTH / 8){1'b0}};
        end else if (w_write_flag & ~w_write) begin
	  	    w_data_0 <= s_axi_wdata;
            w_strb_0 <= s_axi_wstrb;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_resp_0 <= 2'b0;
        end else if (b_write_flag & ~b_write) begin
            if (err_write_i) begin
                b_resp_0 <= 2'b10;
            else begin
	  	        b_resp_0 <= m_axi_bresp;
            end
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_addr_0 <= {ADDR_WIDTH{1'b0}};
            ar_prot_0 <= 3'b0;
        end else if (ar_write_flag & ~ar_write) begin
	  	    ar_addr_0 <= s_axi_araddr;
            ar_prot_0 <= s_axi_arprot;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_data_0 <= {DATA_WIDTH{1'b0}};
            r_resp_0 <= 2'b0;
        end else if (r_write_flag & ~r_write) begin
	  	    r_data_0 <= m_axi_rdata;
            if (err_read_i) begin
                r_resp_0 <= 2'b10;
            else begin
                r_resp_0 <= m_axi_rresp;
            end
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_addr_1 <= {ADDR_WIDTH{1'b0}};
            aw_prot_1 <= 3'b0;
        end else if (aw_write_flag & aw_write) begin
	  	    aw_addr_1 <= s_axi_awaddr;
            aw_prot_1 <= s_axi_awprot;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_data_1 <= {DATA_WIDTH{1'b0}};
            w_strb_1 <= {(DATA_WIDTH / 8){1'b0}};
        end else if (w_write_flag & w_write) begin
	  	    w_data_1 <= s_axi_wdata;
            w_strb_1 <= s_axi_wstrb;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_resp_1 <= 2'b0;
        end else if (b_write_flag & b_write) begin
            if (err_write_i) begin
                b_resp_1 <= 2'b10;
            else begin
	  	        b_resp_1 <= m_axi_bresp;
            end
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_addr_1 <= {ADDR_WIDTH{1'b0}};
            ar_prot_1 <= 3'b0;
        end else if (ar_write_flag & ar_write) begin
	  	    ar_addr_1 <= s_axi_araddr;
            ar_prot_1 <= s_axi_arprot;
	  	end
    end

    always @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_data_1 <= {DATA_WIDTH{1'b0}};
            r_resp_1 <= 2'b0;
        end else if (r_write_flag & r_write) begin
	  	    r_data_1 <= m_axi_rdata;
            if (err_read_i) begin
                r_resp_1 <= 2'b10;
            else begin
                r_resp_1 <= m_axi_rresp;
            end
	  	end
    end
