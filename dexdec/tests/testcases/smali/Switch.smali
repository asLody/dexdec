.class public LSwitch;
.super Ljava/lang/Object;
.source "Switch.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static dayName(I)Ljava/lang/String;
    .registers 1

    .line 4
    packed-switch p0, :pswitch_data_1c

    .line 12
    const-string p0, "Invalid"

    return-object p0

    .line 11
    :pswitch_6
    const-string p0, "Sunday"

    return-object p0

    .line 10
    :pswitch_9
    const-string p0, "Saturday"

    return-object p0

    .line 9
    :pswitch_c
    const-string p0, "Friday"

    return-object p0

    .line 8
    :pswitch_f
    const-string p0, "Thursday"

    return-object p0

    .line 7
    :pswitch_12
    const-string p0, "Wednesday"

    return-object p0

    .line 6
    :pswitch_15
    const-string p0, "Tuesday"

    return-object p0

    .line 5
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
