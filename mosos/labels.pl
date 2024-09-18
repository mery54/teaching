# LaTeX2HTML 2024 (Released January 1, 2024)
# Associate labels original text with physical files.


$key = q/cite_losl-b/;
$external_labels{$key} = "$URL/" . q|node4.html|; 
$noresave{$key} = "$nosave";

$key = q/cite_losl-eatcs/;
$external_labels{$key} = "$URL/" . q|node4.html|; 
$noresave{$key} = "$nosave";

$key = q/sec:course-mcfsi-at/;
$external_labels{$key} = "$URL/" . q|node2.html|; 
$noresave{$key} = "$nosave";

$key = q/sec:course-modell-verify/;
$external_labels{$key} = "$URL/" . q|node3.html|; 
$noresave{$key} = "$nosave";

1;


# LaTeX2HTML 2024 (Released January 1, 2024)
# labels from external_latex_labels array.


$key = q/sec:course-mcfsi-at/;
$external_latex_labels{$key} = q|2 Course MCFSI at Telecom Nancy|; 
$noresave{$key} = "$nosave";

$key = q/sec:course-modell-verify/;
$external_latex_labels{$key} = q|3 Course Modelling and verifying software-based systems|; 
$noresave{$key} = "$nosave";

1;

