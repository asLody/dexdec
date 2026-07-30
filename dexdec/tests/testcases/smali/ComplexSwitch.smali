.class public LComplexSwitch;
.super Ljava/lang/Object;
.source "ComplexSwitch.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static categorize(I)I
    .registers 1

    .line 6
    packed-switch p0, :pswitch_data_c

    .line 17
    const/4 p0, 0x3

    goto :goto_a

    .line 14
    :pswitch_5
    nop

    .line 15
    const/4 p0, 0x2

    goto :goto_a

    .line 10
    :pswitch_8
    nop

    .line 11
    const/4 p0, 0x1

    .line 20
    :goto_a
    return p0

    nop

    :pswitch_data_c
    .packed-switch 0x1
        :pswitch_8
        :pswitch_8
        :pswitch_8
        :pswitch_5
        :pswitch_5
    .end packed-switch
.end method

.method public static dayName(I)Ljava/lang/String;
    .registers 1

    .line 25
    packed-switch p0, :pswitch_data_1c

    .line 41
    const-string p0, "Invalid"

    return-object p0

    .line 39
    :pswitch_6
    const-string p0, "Sunday"

    return-object p0

    .line 37
    :pswitch_9
    const-string p0, "Saturday"

    return-object p0

    .line 35
    :pswitch_c
    const-string p0, "Friday"

    return-object p0

    .line 33
    :pswitch_f
    const-string p0, "Thursday"

    return-object p0

    .line 31
    :pswitch_12
    const-string p0, "Wednesday"

    return-object p0

    .line 29
    :pswitch_15
    const-string p0, "Tuesday"

    return-object p0

    .line 27
    :pswitch_18
    const-string p0, "Monday"

    return-object p0

    nop

    :pswitch_data_1c
    .packed-switch 0x1
        :pswitch_18
        :pswitch_15
        :pswitch_12
        :pswitch_f
        :pswitch_c
        :pswitch_9
        :pswitch_6
    .end packed-switch
.end method

.method public static nestedSwitch(II)I
    .registers 2

    .line 47
    nop

    .line 48
    packed-switch p0, :pswitch_data_1a

    .line 66
    const/4 p0, 0x0

    goto :goto_18

    .line 63
    :pswitch_6
    nop

    .line 64
    const/16 p0, 0x14

    goto :goto_18

    .line 50
    :pswitch_a
    packed-switch p1, :pswitch_data_22

    .line 58
    nop

    .line 59
    const/16 p0, 0xa

    goto :goto_18

    .line 55
    :pswitch_11
    nop

    .line 56
    const/16 p0, 0xc

    goto :goto_18

    .line 52
    :pswitch_15
    nop

    .line 53
    const/16 p0, 0xb

    .line 69
    :goto_18
    return p0

    nop

    :pswitch_data_1a
    .packed-switch 0x1
        :pswitch_a
        :pswitch_6
    .end packed-switch

    :pswitch_data_22
    .packed-switch 0x1
        :pswitch_15
        :pswitch_11
    .end packed-switch
.end method
