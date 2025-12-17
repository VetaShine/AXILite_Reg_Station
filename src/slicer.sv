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
    logic [ADDR_WIDTH - 1 : 0]       aw_addr       ;
    logic [2 : 0]                    aw_prot       ;
    logic                            aw_fifo_status;

    logic [DATA_WIDTH - 1 : 0]       w_data	       ;
    logic [(DATA_WIDTH / 8) - 1 : 0] w_strb	       ;
    logic                            w_fifo_status ;

    logic [1 : 0]                    b_resp	       ;
    logic [1 : 0]                    b_fifo_status ;

    logic [ADDR_WIDTH - 1 : 0]       ar_addr       ;
    logic [2 : 0]                    ar_prot       ;
    logic                            ar_fifo_status;

    logic [DATA_WIDTH - 1 : 0]       r_data	       ;
    logic [1 : 0]                    r_resp	       ;
    logic                            r_fifo_status ;

    logic                            aw_err	       ;
    logic                            w_err	       ;
    logic                            aw_stored     ;
    logic                            w_stored      ;


    assign aw_write_flag = s_axi_awvalid & s_axi_awready;
    assign aw_read_flag  = m_axi_awvalid & m_axi_awready;

    assign w_write_flag  = s_axi_wvalid & s_axi_wready;
    assign w_read_flag   = m_axi_wvalid & m_axi_wready;

    assign b_write_flag  = m_axi_bvalid & m_axi_bready;
    assign b_read_flag   = s_axi_bvalid & s_axi_bready;

    assign ar_write_flag = s_axi_arvalid & s_axi_arready;
    assign ar_read_flag  = m_axi_arvalid & m_axi_arready;

    assign r_write_flag  = m_axi_rvalid & m_axi_rready;
    assign r_read_flag   = s_axi_rvalid & s_axi_rready;

    assign write_accepted = m_axi_awvalid && m_axi_awready && m_axi_wvalid && m_axi_wready;


    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_fifo_status <= 1'b0;
        end else if (aw_write_flag & ~aw_read_flag) begin
            aw_fifo_status <= 1'b1;
        end else if (b_read_flag) begin
            aw_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_fifo_status <= 1'b0;
        end else if (w_write_flag & ~w_read_flag) begin
            w_fifo_status <= 1'b1;
        end else if (b_read_flag) begin
            w_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_fifo_status <= 1'b0;
        end else if (b_write_flag & ~b_read_flag) begin
            b_fifo_status <= 1'b1;
        end else if (~b_write_flag & b_read_flag) begin
            b_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_fifo_status <= 1'b0;
        end else if (ar_write_flag & ~ar_read_flag) begin
            ar_fifo_status <= 1'b1;
        end else if (r_read_flag) begin
            ar_fifo_status <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_fifo_status <= 1'b0;
        end else if (r_write_flag & ~r_read_flag) begin
            r_fifo_status <= 1'b1;
        end else if (~r_write_flag & r_read_flag) begin
            r_fifo_status <= 1'b0;
        end
    end

    assign s_axi_awready = ~aw_fifo_status;
    assign s_axi_wready  = ~w_fifo_status ;
    assign m_axi_bready  = ~b_fifo_status ;
    assign s_axi_arready = ~ar_fifo_status;
    assign m_axi_rready  = ~r_fifo_status ;

    assign m_axi_awvalid  = aw_stored & w_stored & ~aw_err & ~w_err;
    assign m_axi_wvalid   = aw_stored & w_stored & ~aw_err & ~w_err;
    assign bvalid_for_err = (err_awrite_i || err_write_i || aw_err || w_err) & aw_stored & w_stored;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_bvalid <= 1'b0;
        end else if (b_read_flag & ~b_write_flag) begin
            s_axi_bvalid <= 1'b0;
        end else if (b_write_flag & ~b_read_flag) begin
            s_axi_bvalid <= 1'b1;
        end else if (bvalid_for_err) begin
            s_axi_bvalid <= 1'b1;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            m_axi_arvalid <= 1'b0;
        end else if (ar_read_flag & ~ar_write_flag) begin
            m_axi_arvalid <= 1'b0;
        end else if (ar_write_flag & ~ar_read_flag & ~err_read_i) begin
            m_axi_arvalid <= 1'b1;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            s_axi_rvalid <= 1'b0;
        end else if (r_read_flag & ~r_write_flag) begin
            s_axi_rvalid <= 1'b0;
        end else if (r_write_flag & ~r_read_flag) begin
            s_axi_rvalid <= 1'b1;
        end else if (err_read_i & ar_write_flag) begin
            s_axi_rvalid <= 1'b1;
        end
    end

    assign m_axi_awaddr = aw_addr;
    assign m_axi_awprot = aw_prot;
    assign m_axi_wdata  = w_data ;
    assign m_axi_wstrb  = w_strb ;
    assign s_axi_bresp  = b_resp ;
    assign m_axi_araddr = ar_addr;
    assign m_axi_arprot = ar_prot;
    assign s_axi_rdata  = r_data ;
    assign s_axi_rresp  = r_resp ;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            aw_stored <= 1'b0;
        end else if (aw_write_flag) begin
            aw_stored <= 1'b1;
        end else if (write_accepted) begin
            aw_stored <= 1'b0;
        end else if (bvalid_for_err) begin
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
        end else if (bvalid_for_err) begin
            w_stored <= 1'b0;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            aw_addr <= {ADDR_WIDTH{1'b0}};
            aw_prot <= 3'b0;
            aw_err  <= 1'b0;
        end else if (aw_write_flag) begin
            aw_addr <= s_axi_awaddr;
            aw_prot <= s_axi_awprot;
            aw_err  <= err_awrite_i;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            w_data <= {DATA_WIDTH{1'b0}};
            w_strb <= {(DATA_WIDTH / 8){1'b0}};
            w_err  <= 1'b0;
        end else if (w_write_flag) begin
            w_data <= s_axi_wdata;
            w_strb <= s_axi_wstrb;
            w_err  <= err_write_i;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            b_resp <= 2'b0;
        end else if (b_write_flag) begin
            b_resp <= m_axi_bresp;
        end else if (bvalid_for_err) begin
            b_resp <= 2'b10;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            ar_addr <= {ADDR_WIDTH{1'b0}};
            ar_prot <= 3'b0;
        end else if (ar_write_flag) begin
            ar_addr <= s_axi_araddr;
            ar_prot <= s_axi_arprot;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_data <= {DATA_WIDTH{1'b0}};
        end else if (r_write_flag) begin
            r_data <= m_axi_rdata;
        end 
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (~aresetn) begin
            r_resp <= 2'b0;
        end else if (r_write_flag || err_read_i) begin
            r_resp <= err_read_i ? 2'b10 : m_axi_rresp;
        end 
    end
endmodule
