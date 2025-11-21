module protocol_checker #(
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32,
    parameter bit ERR_RESP_EN   = 1'b0
) (
    input  logic [ADDR_WIDTH - 1 : 0]        s_axi_awaddr ,
    input  logic                             s_axi_awvalid,
    input  logic [2 : 0]                     s_axi_awprot ,

    input  logic [DATA_WIDTH - 1 : 0]        s_axi_wdata  ,
    input  logic [(DATA_WIDTH / 8) - 1 : 0]  s_axi_wstrb  ,
    input  logic                             s_axi_wvalid ,

    input  logic [ADDR_WIDTH - 1 : 0]        s_axi_araddr ,
    input  logic                             s_axi_arvalid,
    input  logic [2 : 0]                     s_axi_arprot ,

    output logic                             err_write_o  ,
    output logic                             err_read_o
);
    if (ERR_RESP_EN) begin: gen_enabled
        localparam int ALIGN_BITS = $clog2(DATA_WIDTH / 8);

        wire aw_addr_misaligned = s_axi_awvalid && |s_axi_awaddr[ALIGN_BITS - 1 : 0];
        wire ar_addr_misaligned = s_axi_arvalid && |s_axi_araddr[ALIGN_BITS - 1 : 0];

        wire wstrb_zero = s_axi_wvalid && (s_axi_wstrb == {(DATA_WIDTH / 8){1'b0}});

        assign err_write_o = aw_addr_misaligned || wstrb_zero;
        assign err_read_o  = ar_addr_misaligned;
    end else begin: get_disabled
        assign err_write_o = 1'b0;
        assign err_read_o  = 1'b0;
    end
endmodule