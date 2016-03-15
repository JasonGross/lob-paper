Run, chrome.exe https://icfp2016.hotcrp.com/paper/14/edit
WinWait, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
IfWinNotActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window, WinActivate, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
WinWaitActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
Send, {CTRLDOWN}e{CTRLUP}
Sleep, 500
Send, {BACKSPACE}javascript:document.getElementById('paperUpload').click(){ENTER}
WinWait, Open, Namespace Tree Contr
IfWinNotActive, Open, Namespace Tree Contr, WinActivate, Open, Namespace Tree Contr
WinWaitActive, Open, Namespace Tree Contr
Send, D:\Documents\GitHub\lob-paper\lob-preprint.pdf{ENTER}
WinWait, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
IfWinNotActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window, WinActivate, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
WinWaitActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
Send, {CTRLDOWN}e{CTRLUP}
Sleep, 500
Send, {BACKSPACE}javascript:((function (foo) {{} for (var i = 0; i < foo.length; i{+}{+}) if (foo[i].id.match('{^}remover')) foo[i].click(); {}})(document.getElementsByTagName('a'))){ENTER}
Send, {CTRLDOWN}f{CTRLUP}
; Sleep, 500
; Send, {TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{ENTER}
Send, 0{BACKSPACE}add{SPACE}attachment{ESC}{ENTER}
WinWait, Open, Namespace Tree Contr
IfWinNotActive, Open, Namespace Tree Contr, WinActivate, Open, Namespace Tree Contr
WinWaitActive, Open, Namespace Tree Contr
Send, D:\Documents\GitHub\lob-paper\supplemental-anonymous.zip{ENTER}
WinWait, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
IfWinNotActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window, WinActivate, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
WinWaitActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
Send, {CTRLDOWN}f{CTRLUP}
; Sleep, 500
; Send, {TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{TAB}{ENTER}
Send, 0{BACKSPACE}add{SPACE}attachment{ENTER}{ESC}{ENTER}
WinWait, Open, Namespace Tree Contr
IfWinNotActive, Open, Namespace Tree Contr, WinActivate, Open, Namespace Tree Contr
WinWaitActive, Open, Namespace Tree Contr
Send, D:\Documents\GitHub\lob-paper\supplemental-nonymous.zip{ENTER}
WinWait, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
IfWinNotActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window, WinActivate, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
WinWaitActive, #14 - ICFP 2016 - Google Chrome, Chrome Legacy Window
Send, {CTRLDOWN}e{CTRLUP}
Sleep, 500
Send, {SHIFTDOWN}{TAB}{TAB}{TAB}{TAB}{SHIFTUP}
