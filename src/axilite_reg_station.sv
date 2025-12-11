module axi4lite_reg_station #(
    parameter int ADDR_WIDTH    = 32  ,
    parameter int DATA_WIDTH    = 32  ,
    parameter bit ERR_RESP_EN   = 1'b0,
    parameter bit IRQ_EN        = 1'b0,
    parameter int IRQ_HOLD_TIME = 1024,
    parameter bit RST_SYNC_EN   = 1'b0 
) (
    input  logic                             aclk         ,
    input  logic                             aresetn      ,

    // Interrupt
    output logic                             irq_o        ,

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
    localparam int ADDR_WIDTH_ACTUAL    = (ADDR_WIDTH >= 32 && ADDR_WIDTH <= 64) ? ADDR_WIDTH : 32;
    localparam int DATA_WIDTH_ACTUAL    = (DATA_WIDTH == 32 || DATA_WIDTH == 64) ? DATA_WIDTH : 32;
    localparam int IRQ_HOLD_TIME_ACTUAL = (IRQ_HOLD_TIME >= 1 && IRQ_HOLD_TIME <= 65536) ? IRQ_HOLD_TIME : 1024;

    logic reset      ;
    logic err_write_o;
    logic err_read_o ;

    rst_sync #(
        .RST_SYNC_EN(RST_SYNC_EN)
    ) u_rst_sync (
        .clk      (aclk)   ,
        .aresetn  (aresetn),
        .reset_out(reset)
    );

    irq_gen #(
        .ERR_RESP_EN  (ERR_RESP_EN)         ,
        .IRQ_EN       (IRQ_EN)              ,
        .IRQ_HOLD_TIME(IRQ_HOLD_TIME_ACTUAL)
    ) u_irq_gen (
        .aclk   (aclk) ,
        .rstn   (reset),
        .error_i(err_write_o || err_read_o),
        .irq_o  (irq_o)
    );

    protocol_checker #(
        .ADDR_WIDTH (ADDR_WIDTH_ACTUAL),
        .DATA_WIDTH (DATA_WIDTH_ACTUAL),
        .ERR_RESP_EN(ERR_RESP_EN)
    ) u_protocol_checker (
        .s_axi_awaddr (s_axi_awaddr) ,
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awprot (s_axi_awprot) ,
        .s_axi_wdata  (s_axi_wdata)  ,
        .s_axi_wstrb  (s_axi_wstrb)  ,
        .s_axi_wvalid (s_axi_wvalid) ,
        .s_axi_araddr (s_axi_araddr) ,
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arprot (s_axi_arprot) ,
        .err_write_o  (err_write_o)  ,
        .err_read_o   (err_read_o)
    );

    slicer #(
        .ADDR_WIDTH(ADDR_WIDTH_ACTUAL),
        .DATA_WIDTH(DATA_WIDTH_ACTUAL)
    ) u_slicer (
        .aclk         (aclk)         ,
        .aresetn      (reset)        ,
        .err_write_i  (err_write_o)  ,
        .err_read_i   (err_read_o)   ,
        .s_axi_awaddr (s_axi_awaddr) ,
        .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_awprot (s_axi_awprot) ,
        .s_axi_wdata  (s_axi_wdata)  ,
        .s_axi_wstrb  (s_axi_wstrb)  ,
        .s_axi_wvalid (s_axi_wvalid) ,
        .s_axi_wready (s_axi_wready) ,
        .s_axi_bresp  (s_axi_bresp)  ,
        .s_axi_bvalid (s_axi_bvalid) ,
        .s_axi_bready (s_axi_bready) ,
        .s_axi_araddr (s_axi_araddr) ,
        .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_arprot (s_axi_arprot) ,
        .s_axi_rdata  (s_axi_rdata)  ,
        .s_axi_rvalid (s_axi_rvalid) ,
        .s_axi_rready (s_axi_rready) ,
        .s_axi_rresp  (s_axi_rresp)  ,
        .m_axi_awaddr (m_axi_awaddr) ,
        .m_axi_awvalid(m_axi_awvalid),
        .m_axi_awready(m_axi_awready),
        .m_axi_awprot (m_axi_awprot) ,
        .m_axi_wdata  (m_axi_wdata)  ,
        .m_axi_wstrb  (m_axi_wstrb)  ,
        .m_axi_wvalid (m_axi_wvalid) ,
        .m_axi_wready (m_axi_wready) ,
        .m_axi_bresp  (m_axi_bresp)  ,
        .m_axi_bvalid (m_axi_bvalid) ,
        .m_axi_bready (m_axi_bready) ,
        .m_axi_araddr (m_axi_araddr) ,
        .m_axi_arvalid(m_axi_arvalid),
        .m_axi_arready(m_axi_arready),
        .m_axi_arprot (m_axi_arprot) ,
        .m_axi_rdata  (m_axi_rdata)  ,
        .m_axi_rvalid (m_axi_rvalid) ,
        .m_axi_rready (m_axi_rready) ,
        .m_axi_rresp  (m_axi_rresp)
    );
endmodule
