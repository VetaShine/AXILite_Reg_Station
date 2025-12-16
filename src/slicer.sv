module slicer #(
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32
) (
    input  logic                             aclk         ,
    input  logic                             aresetn	  ,
    input  logic                             err_awrite_i ,
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
    logic [ADDR_WIDTH - 1 : 0]       aw_addr_0     ;
    logic [2 : 0]                    aw_prot_0     ;
    logic [1 : 0]                    aw_fifo_status;

    logic [DATA_WIDTH - 1 : 0]       w_data_0	   ;
    logic [(DATA_WIDTH / 8) - 1 : 0] w_strb_0	   ;
    logic [1 : 0]                    w_fifo_status ;

    logic [1 : 0]                    b_resp_0	   ;
    logic [1 : 0]                    b_fifo_status ;

    logic [ADDR_WIDTH - 1 : 0]       ar_addr_0     ;
    logic [2 : 0]                    ar_prot_0     ;
    logic                            ar_fifo_status;

    logic [DATA_WIDTH - 1 : 0]       r_data_0	   ;
    logic [1 : 0]                    r_resp_0	   ;
    logic                            r_fifo_status ;

    logic                            r_err_0	   ;
    logic                            aw_err_0	   ;
    logic                            w_err_0	   ;
    logic                            aw_stored     ;
    logic                            w_stored      ;


    assign aw_write_flag = s_axi_awvalid & s_axi_awready;
    assign aw_read_flag  = m_axi_awvalid & m_axi_awready;
    assign aw_empty	     = (aw_fifo_status == 0);
    assign aw_full	     = aw_fifo_status;

    assign w_write_flag  = s_axi_wvalid & s_axi_wready;
    assign w_read_flag   = m_axi_wvalid & m_axi_wready;
    assign w_empty	     = (w_fifo_status == 0);
    assign w_full        = w_fifo_status;

    assign b_write_flag  = m_axi_bvalid & m_axi_bready;
    assign b_read_flag   = s_axi_bvalid & s_axi_bready;
    assign b_empty	     = (b_fifo_status == 0);
    assign b_full        = b_fifo_status;

    assign ar_write_flag = s_axi_arvalid & s_axi_arready;
    assign ar_read_flag  = m_axi_arvalid & m_axi_arready;
    assign ar_empty	     = (ar_fifo_status == 0);
    assign ar_full	     = ar_fifo_status;

    assign r_write_flag  = m_axi_rvalid & m_axi_rready;
    assign r_read_flag   = s_axi_rvalid & s_axi_rready;
    assign r_empty	     = (r_fifo_status == 0);
    assign r_full        = r_fifo_status;

    assign write_accepted = m_axi_awvalid && m_axi_awready && m_axi_wvalid && m_axi_wready;
    assign write_ready    = aw_stored && w_stored;


    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_fifo_status <= 2'b0;
        end else if (aw_write_flag & ~aw_read_flag) begin
            aw_fifo_status <= 1'b1;
        end else if (b_read_flag) begin
            aw_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_fifo_status <= 2'b0;
        end else if (w_write_flag & ~w_read_flag) begin
            w_fifo_status <= 1'b1;
        end else if (b_read_flag) begin
            w_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_fifo_status <= 2'b0;
        end else if (b_write_flag & ~b_read_flag) begin
            b_fifo_status <= 1'b1;
        end else if (~b_write_flag & b_read_flag) begin
            b_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_fifo_status <= 2'b0;
        end else if (ar_write_flag & ~ar_read_flag) begin
            ar_fifo_status <= 1'b1;
        end else if (s_axi_rvalid & s_axi_rready) begin
            ar_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_fifo_status <= 2'b0;
        end else if (r_write_flag & ~r_read_flag) begin
            r_fifo_status <= 1'b1;
        end else if (~r_write_flag & r_read_flag) begin
            r_fifo_status <= 1'b0;
        end
    end

    assign s_axi_awready = ~aw_full;
    assign s_axi_wready  = ~w_full ;
    assign m_axi_bready  = ~b_full ;
    assign s_axi_arready = ~ar_full;
    assign m_axi_rready  = ~r_full ;

    assign m_axi_awvalid = write_ready;
    assign m_axi_wvalid  = write_ready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_bvalid <= 1'b0;
        end else if ((b_fifo_status == 1) & b_read_flag & ~b_write_flag) begin
            s_axi_bvalid <= 1'b0;
        end else if (b_empty & b_write_flag & ~b_read_flag) begin
            s_axi_bvalid <= 1'b1;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            m_axi_arvalid <= 1'b0;
        end else if ((ar_fifo_status == 1) & ar_read_flag & ~ar_write_flag) begin
            m_axi_arvalid <= 1'b0;
        end else if (ar_empty & ar_write_flag & ~ar_read_flag) begin
            m_axi_arvalid <= 1'b1;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_rvalid <= 1'b0;
        end else if ((r_fifo_status == 1) & r_read_flag & ~r_write_flag) begin
            s_axi_rvalid <= 1'b0;
        end else if (r_empty & r_write_flag & ~r_read_flag) begin
            s_axi_rvalid <= 1'b1;
        end
    end

    assign m_axi_awaddr = aw_addr_0;
    assign m_axi_awprot = aw_prot_0;
    assign m_axi_wdata  = w_data_0 ;
    assign m_axi_wstrb  = w_strb_0 ;
    assign s_axi_bresp  = b_resp_0 ;
    assign m_axi_araddr = ar_addr_0;
    assign m_axi_arprot = ar_prot_0;
    assign s_axi_rdata  = r_data_0 ;
    assign s_axi_rresp  = r_resp_0 ;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            aw_stored <= 1'b0;
        end else if (aw_write_flag) begin
            aw_stored <= 1'b1;
        end else if (write_accepted) begin
            aw_stored <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            w_stored  <= 1'b0;
        end else if (w_write_flag) begin
            w_stored <= 1'b1;
        end else if (write_accepted) begin
            w_stored  <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_addr_0 <= {ADDR_WIDTH{1'b0}};
            aw_prot_0 <= 3'b0;
            aw_err_0  <= 1'b0;
        end else if (aw_write_flag) begin
            aw_addr_0 <= s_axi_awaddr;
            aw_prot_0 <= s_axi_awprot;
            aw_err_0  <= err_awrite_i;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_data_0 <= {DATA_WIDTH{1'b0}};
            w_strb_0 <= {(DATA_WIDTH / 8){1'b0}};
            w_err_0  <= 1'b0;
        end else if (w_write_flag) begin
            w_data_0 <= s_axi_wdata;
            w_strb_0 <= s_axi_wstrb;
            w_err_0  <= err_write_i;
        end
    end

        always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_resp_0 <= 2'b0;
        end else if (b_write_flag) begin
            b_resp_0 <= (aw_err_0 || w_err_0) ? 2'b10 : m_axi_bresp;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_addr_0 <= {ADDR_WIDTH{1'b0}};
            ar_prot_0 <= 3'b0;
            r_err_0   <= 1'b0;
        end else if (ar_write_flag) begin
            ar_addr_0 <= s_axi_araddr;
            ar_prot_0 <= s_axi_arprot;
            r_err_0   <= err_read_i;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_data_0 <= {DATA_WIDTH{1'b0}};
            r_resp_0 <= 2'b0;
        end else if (r_write_flag) begin
            r_data_0 <= m_axi_rdata;
            r_resp_0 <= r_err_0 ? 2'b10 : m_axi_rresp;
        end
    end
endmodule
