{{- define "pf-enforce.fullname" -}}
{{- if .Chart.Name -}}{{ .Chart.Name }}{{- else -}}pf-enforce{{- end -}}
{{- end -}}

{{- define "pf-enforce.serviceAccountName" -}}
{{- if .Values.rbac.serviceAccount.name }}{{ .Values.rbac.serviceAccount.name }}{{ else }}pf-enforce-admission{{ end -}}
{{- end -}}
