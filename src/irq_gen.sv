module irq_gen #(
    parameter bit ERR_RESP_EN   = 1'b0,
    parameter bit IRQ_EN        = 1'b0,
    parameter int IRQ_HOLD_TIME = 1024
) (
    input  logic aclk   ,
    input  logic rstn   ,
    input  logic error_i,
    output logic irq_o
);
    if (ERR_RESP_EN && IRQ_EN) begin: gen_enabled
        localparam int CNT_W = $clog2(IRQ_HOLD_TIME + 1);
        logic [CNT_W - 1 : 0] cnt;
        logic active;

        always_ff @(posedge aclk or negedge rstn) begin
            if (!rstn) begin
                cnt    <= '0;
                active <= 1'b0;
                irq_o  <= 1'b0;
            end else begin
                if (error_i) begin
                    active <= 1'b1;
                    cnt    <= IRQ_HOLD_TIME - 1;
                    irq_o  <= 1'b1;
                end else if (active) begin
                    if (cnt == 0) begin
                        active <= 1'b0;
                        irq_o  <= 1'b0;
                    end else begin
                        cnt   <= cnt - 1;
                        irq_o <= 1'b1;
                    end
                end else begin
                    irq_o <= 1'b0;
                end
            end
        end
    end else begin: get_disabled
        assign irq_o = 1'b0;
    end
endmodule
